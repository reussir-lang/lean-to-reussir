//! Allocation of runtime objects through mimalloc's plain entry points.
//!
//! Reussir's global allocator (`reussir_rt::alloc::ReussirGlobalAlloc`)
//! raises every Rust allocation to 16-byte alignment, above what it treats as
//! mimalloc's natural alignment (8), so *every* Rust `Box`/`Vec` allocation
//! takes mimalloc's aligned path (`mi_malloc_aligned`, `mi_realloc_aligned`),
//! and pages holding aligned blocks send later frees down mimalloc's generic
//! path too. Strings, arrays and big numbers are allocated here instead with
//! `mi_malloc`/`mi_realloc` (mimalloc's blocks of 16 bytes or more are
//! 16-aligned anyway; runtime objects need 8). They are freed normally: the
//! global allocator frees any mimalloc block with `mi_free`.
//!
//! Types aligned above 8 fall back to the standard allocation.

use reussir_rt::rc::Rc;
use std::ffi::c_void;
use std::mem::{align_of, size_of};

extern "C" {
    fn mi_malloc(size: usize) -> *mut c_void;
    fn mi_zalloc(size: usize) -> *mut c_void;
    fn mi_realloc(p: *mut c_void, size: usize) -> *mut c_void;
}

#[cold]
#[inline(never)]
fn oom() -> ! {
    crate::internal_panic("out of memory")
}

/// Mirror of `reussir_rt::rc::RcBox` (`#[repr(C)] { count: Cell<u32>, data }`).
#[repr(C)]
struct RcBoxMirror<T> {
    count: u32,
    data: T,
}

#[inline(always)]
fn plain<T>() -> bool {
    align_of::<T>() <= 8 && size_of::<T>() > 0
}

/// `Rc::new(v)` allocated with `mi_malloc`.
#[inline(always)]
pub fn rc_new<T>(v: T) -> Rc<T> {
    if !plain::<RcBoxMirror<T>>() {
        return Rc::new(v);
    }
    unsafe {
        let p = mi_malloc(size_of::<RcBoxMirror<T>>()) as *mut RcBoxMirror<T>;
        if p.is_null() {
            oom();
        }
        std::ptr::write(p, RcBoxMirror { count: 1, data: v });
        // `Rc<T>` is a `#[repr(transparent)]` pointer to its box.
        std::mem::transmute::<*mut RcBoxMirror<T>, Rc<T>>(p)
    }
}

/// `Box::new(v)` allocated with `mi_malloc`.
#[inline(always)]
pub fn box_new<T>(v: T) -> Box<T> {
    if !plain::<T>() {
        return Box::new(v);
    }
    unsafe {
        let p = mi_malloc(size_of::<T>()) as *mut T;
        if p.is_null() {
            oom();
        }
        std::ptr::write(p, v);
        Box::from_raw(p)
    }
}

/// An empty vector with room for `cap` elements.
#[inline(always)]
pub fn vec_with_capacity<T>(cap: usize) -> Vec<T> {
    if cap == 0 || !plain::<T>() {
        return Vec::with_capacity(cap);
    }
    unsafe {
        let p = mi_malloc(cap.checked_mul(size_of::<T>()).unwrap_or_else(|| oom())) as *mut T;
        if p.is_null() {
            oom();
        }
        Vec::from_raw_parts(p, 0, cap)
    }
}

/// `n` zero words.
#[inline(always)]
pub fn vec_zeroed_u64(n: usize) -> Vec<u64> {
    if n == 0 {
        return Vec::new();
    }
    unsafe {
        let p = mi_zalloc(n.checked_mul(8).unwrap_or_else(|| oom())) as *mut u64;
        if p.is_null() {
            oom();
        }
        Vec::from_raw_parts(p, n, n)
    }
}

/// A copy of a slice, with room for `extra` more elements.
#[inline(always)]
pub fn vec_from_slice<T: Clone>(s: &[T], extra: usize) -> Vec<T> {
    let mut v = vec_with_capacity(s.len() + extra);
    v.extend_from_slice(s);
    v
}

/// Make room for `extra` more elements, growing geometrically (so appends
/// are amortized O(1)) with `mi_realloc` instead of the aligned realloc.
#[inline(always)]
pub fn reserve<T>(v: &mut Vec<T>, extra: usize) {
    let need = v.len() + extra;
    if need > v.capacity() {
        grow(v, need)
    }
}

#[cold]
#[inline(never)]
fn grow<T>(v: &mut Vec<T>, need: usize) {
    if !plain::<T>() {
        v.reserve(need - v.len());
        return;
    }
    let new_cap = need.max(v.capacity().saturating_mul(2)).max(8);
    let bytes = new_cap.checked_mul(size_of::<T>()).unwrap_or_else(|| oom());
    let mut old = std::mem::ManuallyDrop::new(std::mem::take(v));
    let (ptr, len, cap) = (old.as_mut_ptr(), old.len(), old.capacity());
    unsafe {
        let np = if cap == 0 { mi_malloc(bytes) } else { mi_realloc(ptr as *mut c_void, bytes) } as *mut T;
        if np.is_null() {
            oom();
        }
        *v = Vec::from_raw_parts(np, len, new_cap);
    }
}
