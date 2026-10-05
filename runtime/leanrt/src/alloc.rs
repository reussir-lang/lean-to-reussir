//! Allocation of runtime objects through mimalloc's plain entry points.
//!
//! Reussir's global allocator (`reussir_rt::alloc::ReussirGlobalAlloc`)
//! raises every Rust allocation to 16-byte alignment, above what it treats as
//! mimalloc's natural alignment (8), so *every* Rust `Box`/`Vec` allocation
//! takes mimalloc's aligned path (`mi_malloc_aligned`, `mi_realloc_aligned`),
//! and pages holding aligned blocks send later frees down mimalloc's generic
//! path too. Strings, arrays and big numbers are allocated here instead with
//! `mi_malloc`/`mi_realloc`, whose blocks are 8-aligned (Reussir builds
//! mimalloc with `MI_MAX_ALIGN_SIZE=8`), which is all runtime objects need.
//! They are freed normally: the global allocator frees any mimalloc block
//! with `mi_free`.
//!
//! Types aligned above 8 fall back to the standard allocation.
//!
//! This requires reussir_rt's (default) mimalloc allocator backend: with a
//! libc-backed global allocator (sanitizer builds), these blocks would be
//! freed with `free`.

use reussir_rt::rc::Rc;
use std::ffi::{c_int, c_long, c_void};
use std::mem::{align_of, size_of};

extern "C" {
    fn mi_malloc(size: usize) -> *mut c_void;
    fn mi_zalloc(size: usize) -> *mut c_void;
    fn mi_realloc(p: *mut c_void, size: usize) -> *mut c_void;
    fn mi_free(p: *mut c_void);
    fn mi_version() -> c_int;
    fn mi_option_set(option: c_int, value: c_long);
}

/// `mi_option_eager_commit_delay` in mimalloc v2's `mi_option_t` (v2.2.4,
/// which Reussir's `libmimalloc-sys` 0.1.44 bundles, and v2.3). mimalloc v3
/// keeps the slot as `deprecated_eager_commit_delay`; another major version
/// may reuse it, so [`heap_on_huge_pages`] sets it only on a v2.
const MI_OPTION_EAGER_COMMIT_DELAY: c_int = 14;

/// Let `main`'s thread allocate on transparent huge pages, as native Lean
/// does. Called on the process's main thread before `main`'s thread starts
/// (`rt::run_main`, `rt::run_main2`).
///
/// lean-runtime's argument constructor (`.init_array.00100`) allocates
/// before mimalloc's own constructor has run. mimalloc gives that
/// allocation a 32 MiB segment straight from the OS and reserves no arena.
/// The first arena (1 GiB) is then reserved for the first segment of
/// `main`'s thread, the process's second thread. mimalloc v2 delays the
/// first `eager_commit_delay` segments (default 1) of every thread but the
/// first, and a delayed segment may not use large OS pages, so the arena
/// was mapped without `MADV_HUGEPAGE`. With transparent huge pages in
/// `madvise` mode, the heap's first GiB then took one page fault per
/// 4 KiB: `deriv` at size 11 had 263,000 faults and 0.28 s system time,
/// native 2,800 faults and 0.09 s (native's mimalloc v3 advises every
/// arena). Before the constructor (lean-runtime switch, step 3), the main
/// thread reserved the arena, with huge pages. With no delay, the first
/// segment of `main`'s thread, and so the arena, may use them.
///
/// Not set when the environment sets `MIMALLOC_EAGER_COMMIT_DELAY` (any
/// case, as mimalloc reads it), or on a mimalloc other than v2 (v3 has no
/// delay).
pub fn heap_on_huge_pages() {
    use std::os::unix::ffi::OsStrExt;
    let v = unsafe { mi_version() };
    // `MI_MALLOC_VERSION`: major and two digits of minor (224), or since
    // 2.3 also two digits of patch (20302).
    let major = if v >= 10000 { v / 10000 } else { v / 100 };
    if major != 2 {
        return;
    }
    if std::env::vars_os().any(|(k, _)| k.as_bytes().eq_ignore_ascii_case(b"MIMALLOC_EAGER_COMMIT_DELAY")) {
        return;
    }
    unsafe { mi_option_set(MI_OPTION_EAGER_COMMIT_DELAY, 0) }
}

#[cold]
#[inline(never)]
fn oom() -> ! {
    crate::lean_internal_panic(lean_runtime::semantics::panic::InternalPanic::OutOfMemory)
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

/// The value of a uniquely referenced `Rc`, moved out; its box is freed
/// without dropping the value. Boxes from `rc_new` and from `Rc::new` (the
/// global allocator) are both mimalloc blocks.
///
/// # Safety
/// `r` must be unique (count 1).
#[inline(always)]
pub unsafe fn rc_into_inner<T>(r: Rc<T>) -> T {
    debug_assert!(r.is_unique());
    let p = std::mem::transmute::<Rc<T>, *mut RcBoxMirror<T>>(r);
    let v = std::ptr::read(&(*p).data);
    mi_free(p as *mut c_void);
    v
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
