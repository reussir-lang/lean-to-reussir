//! Arrays: Reussir's copy-on-write `reussir_rt::collections::vec::Vec<T>`,
//! in the `#[repr(transparent)]` wrapper `crate::drop::Vec` (which frees
//! them without recursion).
//!
//! That type is a `#[repr(transparent)]` wrapper over
//! `reussir_rt::rc::Rc<std::vec::Vec<T>>` (the FFI contract requires it), so
//! the runtime views it as the `Rc` directly to get slice access, `reserve`,
//! `truncate`, ... Every mutation goes through `make_mut`, which copies a
//! shared buffer first: arrays are values, updated in place only when
//! uniquely referenced, like Lean's.
//!
//! `ByteArray` and `FloatArray` are `RVec<u8>`/`RVec<f64>`.

use crate::drop::Vec as RVec;
use reussir_rt::rc::Rc;
use crate::alloc::{rc_new, reserve, vec_with_capacity};

#[inline(always)]
pub fn into_rc<T: Clone>(v: RVec<T>) -> Rc<Vec<T>> {
    unsafe { std::mem::transmute::<RVec<T>, Rc<Vec<T>>>(v) }
}

#[inline(always)]
pub fn from_rc<T: Clone>(v: Rc<Vec<T>>) -> RVec<T> {
    unsafe { std::mem::transmute::<Rc<Vec<T>>, RVec<T>>(v) }
}

/// Give up an array handle that a texture received (every FFI call
/// consumes its arguments). The common case, a shared handle, is a
/// decrement; freeing the last reference is kept out of line so textures
/// stay small enough for LLVM to inline into Reussir code.
#[inline(always)]
pub fn release<T: Clone>(v: RVec<T>) {
    let r = into_rc(v);
    let c = r.count_ref().get();
    if c == 1 {
        drop_last(r)
    } else {
        r.count_ref().set(c - 1);
        std::mem::forget(r);
    }
}

#[cold]
#[inline(never)]
extern "C" fn drop_last<T: Clone>(r: Rc<Vec<T>>) {
    crate::drop::free_vec::<T>(unsafe { std::mem::transmute::<Rc<Vec<T>>, usize>(r) })
}

#[inline(always)]
pub fn as_slice<T: Clone>(v: &RVec<T>) -> &[T] {
    let r: &Rc<Vec<T>> = unsafe { &*(v as *const RVec<T> as *const Rc<Vec<T>>) };
    r.as_slice()
}

/// Mutable access, copying a shared buffer first (reserving `extra`).
#[inline(always)]
pub fn make_mut<T: Clone>(v: &mut Rc<Vec<T>>, extra: usize) -> &mut Vec<T> {
    if !v.is_unique() {
        // By value: the address of `v` (often a local of the Reussir caller
        // once this is inlined) must not escape, or tail calls are lost.
        unsafe { std::ptr::write(v, copy_shared(std::ptr::read(v), extra)) };
    }
    let vec = unsafe { v.data_mut() };
    reserve(vec, extra);
    vec
}

/// A private copy of a shared array (with room for `extra` more), releasing
/// the shared one.
#[cold]
#[inline(never)]
extern "C" fn copy_shared<T: Clone>(v: Rc<Vec<T>>, extra: usize) -> Rc<Vec<T>> {
    let c = rc_new(copy_from_slice(&v, extra));
    drop(v);
    c
}

/// Append clones of `src` to `v` (which has room for them).
trait ExtendCloned: Sized {
    fn extend_cloned(v: &mut Vec<Self>, src: &[Self]);
}

impl<T: Clone> ExtendCloned for T {
    #[inline(always)]
    default fn extend_cloned(v: &mut Vec<T>, src: &[T]) {
        v.extend_from_slice(src)
    }
}

/// A Reussir record crossing the boundary is `Bridge<Inner>`, a pointer to
/// its box, and `Clone` is the compiler-emitted `<record>_ffi_acquire`, an
/// `rc.inc` (inlined into the copy loop). Under the aarch64 encoding of
/// nullary variants (TBI) a nullary constructor is an immediate whose top
/// byte is a tag and whose address is a static dummy box shared by all of
/// them, and `rc.inc` increments its count unguarded: copying an array full
/// of `nil`s (hash map buckets) made all those increments one serial chain
/// through a single word. The dummy's count is never decremented (Reussir
/// steers decrements of immediates away) and never frees, so these
/// increments are skipped here; real boxes are incremented as `rc.inc` does
/// (the 32-bit count at offset 0; these records are not atomic). Other
/// targets use the immortal encoding: the generic clone there.
impl<X: Clone> ExtendCloned for reussir_rt::bridge::Bridge<X> {
    #[inline(always)]
    fn extend_cloned(v: &mut Vec<Self>, src: &[Self]) {
        if cfg!(target_arch = "aarch64") && std::mem::size_of::<Self>() == 8 && v.capacity() - v.len() >= src.len() {
            let mut scratch: u32 = 0;
            for x in src {
                unsafe {
                    let p = std::mem::transmute_copy::<Self, *mut u32>(x);
                    let q = if (p as usize) >> 56 == 0 { p } else { &mut scratch as *mut u32 };
                    *q = (*q).wrapping_add(1);
                }
            }
            std::hint::black_box(scratch);
            unsafe {
                let n = v.len();
                std::ptr::copy_nonoverlapping(src.as_ptr(), v.as_mut_ptr().add(n), src.len());
                v.set_len(n + src.len());
            }
        } else {
            v.extend_from_slice(src)
        }
    }
}

/// A copy of a slice with room for `extra` more elements.
#[inline(always)]
fn copy_from_slice<T: Clone>(s: &[T], extra: usize) -> Vec<T> {
    let mut v = vec_with_capacity(s.len() + extra);
    T::extend_cloned(&mut v, s);
    v
}

/// An index that the Lean-level proof (or the prelude's bounds check)
/// guarantees to be in range was not: a lean2rr/runtime bug.
#[cold]
#[inline(never)]
extern "C" fn index_bug(i: u64, n: usize) -> ! {
    crate::internal_panic(&format!("array index {} out of bounds {} (runtime invariant)", i, n))
}

#[inline]
pub fn with_capacity<T: Clone>(n: usize) -> RVec<T> {
    from_rc(rc_new(vec_with_capacity(n)))
}

/// Allocations of more elements than this are checked against what the
/// native allocation would do (`check_alloc_slow`) first.
pub const CHECK_THRESHOLD: u64 = 1 << 24;

/// Lean's allocation of an array object of `n` elements of `elem` bytes
/// (`lean_alloc_array`, `lean_alloc_sarray`): `24 + elem * n` bytes, where
/// an overflow is the internal panic `integer overflow in runtime
/// computation` and a failed `malloc` is `out of memory`.
#[inline(always)]
pub fn check_alloc(n: u64, elem: u64) {
    if n > CHECK_THRESHOLD {
        check_alloc_slow(n, elem)
    }
}

#[cold]
#[inline(never)]
extern "C" fn check_alloc_slow(n: u64, elem: u64) {
    // Lean allocates big objects with mimalloc too.
    extern "C" {
        #[link_name = "mi_malloc"]
        fn malloc(n: usize) -> *mut std::ffi::c_void;
        #[link_name = "mi_free"]
        fn free(p: *mut std::ffi::c_void);
    }
    let Some(bytes) = n.checked_mul(elem).and_then(|b| b.checked_add(24)) else {
        crate::internal_panic("integer overflow in runtime computation")
    };
    // Would the native allocation succeed? (It is only reserved, not
    // touched, so this costs no memory. `black_box` keeps the compiler from
    // eliding the malloc/free pair.)
    let p = std::hint::black_box(unsafe { malloc(std::hint::black_box(bytes as usize)) });
    if p.is_null() {
        crate::internal_panic("out of memory")
    }
    unsafe { free(p) };
}

/// `Array.mkEmpty n` (and the scalar-array variants, `elem` bytes per
/// element): Lean's allocation checks, then the capacity asked for, as
/// natively (reserved address space: untouched pages cost no memory).
#[inline(never)]
pub fn with_capacity_checked<T: Clone>(n: u64, elem: u64) -> RVec<T> {
    check_alloc(n, elem);
    with_capacity(n as usize)
}

#[inline]
pub fn empty<T: Clone>() -> RVec<T> {
    from_rc(rc_new(Vec::new()))
}

#[inline(always)]
pub fn size<T: Clone>(v: &RVec<T>) -> u64 {
    as_slice(v).len() as u64
}

/// Element `i`, which must be in bounds.
#[inline(always)]
pub fn get<T: Clone>(v: &RVec<T>, i: u64) -> T {
    let s = as_slice(v);
    match s.get(i as usize) {
        Some(x) => x.clone(),
        None => index_bug(i, s.len()),
    }
}

/// `push`: in place when unique with spare capacity; otherwise grow or copy
/// out of line.
#[inline(always)]
pub fn push<T: Clone>(v: RVec<T>, x: T) -> RVec<T> {
    let mut r = into_rc(v);
    if r.is_unique() {
        let vec = unsafe { r.data_mut() };
        if vec.len() < vec.capacity() {
            vec.push(x);
            return from_rc(r);
        }
    }
    push_slow(r, x)
}

/// `push` when shared or full. A shared array is copied with the capacity
/// `lean_array_push` gives it (its own, unless that is below `2 * size + 1`:
/// then `(capacity + 1) * 2`), so a literal pushing onto a shared empty
/// array of capacity `k` allocates a buffer of `k` elements once.
#[cold]
#[inline(never)]
extern "C" fn push_slow<T: Clone>(mut r: Rc<Vec<T>>, x: T) -> RVec<T> {
    let n = r.len();
    let extra = if r.is_unique() {
        n.max(4)
    } else {
        let cap = r.capacity();
        let want = if cap < 2 * n + 1 { (cap + 1) * 2 } else { cap };
        want.max(n + 1) - n
    };
    make_mut(&mut r, extra).push(x);
    from_rc(r)
}

/// Replace element `i` (in bounds): in place when unique.
#[inline(always)]
pub fn set<T: Clone>(v: RVec<T>, i: u64, x: T) -> RVec<T> {
    let mut r = into_rc(v);
    if r.is_unique() {
        let vec = unsafe { r.data_mut() };
        match vec.get_mut(i as usize) {
            Some(slot) => *slot = x,
            None => index_bug(i, vec.len()),
        }
        return from_rc(r);
    }
    set_slow(r, i, x)
}

#[cold]
#[inline(never)]
extern "C" fn set_slow<T: Clone>(mut r: Rc<Vec<T>>, i: u64, x: T) -> RVec<T> {
    let vec = make_mut(&mut r, 0);
    match vec.get_mut(i as usize) {
        Some(slot) => *slot = x,
        None => index_bug(i, vec.len()),
    }
    from_rc(r)
}

/// Drop the last element (no-op when empty).
#[inline(always)]
pub fn pop<T: Clone>(v: RVec<T>) -> RVec<T> {
    let mut r = into_rc(v);
    if r.is_empty() {
        return from_rc(r);
    }
    if r.is_unique() {
        unsafe { r.data_mut() }.pop();
        return from_rc(r);
    }
    pop_slow(r)
}

#[cold]
#[inline(never)]
extern "C" fn pop_slow<T: Clone>(mut r: Rc<Vec<T>>) -> RVec<T> {
    make_mut(&mut r, 0).pop();
    from_rc(r)
}

/// Swap elements `i` and `j` (both in bounds).
#[inline(always)]
pub fn swap<T: Clone>(v: RVec<T>, i: u64, j: u64) -> RVec<T> {
    let mut r = into_rc(v);
    let n = r.len();
    if (i as usize) >= n || (j as usize) >= n {
        index_bug(i.max(j), n);
    }
    if r.is_unique() {
        unsafe { r.data_mut() }.swap(i as usize, j as usize);
        return from_rc(r);
    }
    swap_slow(r, i, j)
}

#[cold]
#[inline(never)]
extern "C" fn swap_slow<T: Clone>(mut r: Rc<Vec<T>>, i: u64, j: u64) -> RVec<T> {
    make_mut(&mut r, 0).swap(i as usize, j as usize);
    from_rc(r)
}

/// `Array.replicate n x`.
#[inline(never)]
pub fn replicate<T: Clone>(n: u64, x: T) -> RVec<T> {
    {
    check_alloc(n, 8);
    let mut v = vec_with_capacity(n as usize);
    v.resize(n as usize, x);
    from_rc(rc_new(v))
}
}

/// Drop elements from index `n` on.
#[inline]
pub fn truncate<T: Clone>(v: RVec<T>, n: u64) -> RVec<T> {
    if (n as usize) >= as_slice(&v).len() {
        return v;
    }
    let mut r = into_rc(v);
    make_mut(&mut r, 0).truncate(n as usize);
    from_rc(r)
}

/// `a ++ b`.
#[inline(never)]
pub fn append<T: Clone>(a: RVec<T>, b: RVec<T>) -> RVec<T> {
    let bs = as_slice(&b);
    if bs.is_empty() {
        return a;
    }
    let mut r = into_rc(a);
    T::extend_cloned(make_mut(&mut r, bs.len()), bs);
    from_rc(r)
}

/// Elements `[start, stop)` (clamped), for `Array.extract`-like primitives.
#[inline(never)]
pub fn extract<T: Clone>(v: RVec<T>, start: u64, stop: u64) -> RVec<T> {
    let s = as_slice(&v);
    let stop = (stop as usize).min(s.len());
    let start = (start as usize).min(stop);
    if start == 0 && stop == s.len() {
        return v;
    }
    from_rc(rc_new(copy_from_slice(&s[start..stop], 0)))
}

/// Reverse in place.
#[inline(never)]
pub fn reverse<T: Clone>(v: RVec<T>) -> RVec<T> {
    let mut r = into_rc(v);
    make_mut(&mut r, 0).reverse();
    from_rc(r)
}

// ---- byte arrays and strings -----------------------------------------------

/// A byte vector as a `ByteArray`.
#[inline]
pub fn bytes_of_vec(v: Vec<u8>) -> RVec<u8> {
    from_rc(rc_new(v))
}

/// `String.toUTF8`: a copy of the bytes, as natively.
#[inline(never)]
pub fn bytes_of_string(s: crate::string::LStr) -> RVec<u8> {
    bytes_of_vec(crate::string::into_vec(s))
}

/// `String.fromUTF8` of valid UTF-8 (counting the characters): a copy of
/// the bytes, as natively.
#[inline(never)]
pub fn string_of_bytes(b: RVec<u8>) -> crate::string::LStr {
    let r = into_rc(b);
    let s = crate::string::from_bytes(&r);
    drop(r);
    s
}

/// `ByteArray.copySlice src srcOff dest destOff len exact`.
#[inline(never)]
pub fn copy_slice(src: RVec<u8>, src_off: u64, dest: RVec<u8>, dest_off: u64, len: u64, exact: bool) -> RVec<u8> {
    let s = as_slice(&src);
    let ssz = s.len();
    if src_off > ssz as u64 {
        return dest;
    }
    let src_off = src_off as usize;
    let len = (len.min(u64::MAX / 2) as usize).min(ssz - src_off);
    let dsz = as_slice(&dest).len();
    let dest_off = (dest_off as usize).min(dsz);
    let new_size = (dest_off + len).max(dsz);
    let _ = exact;
    let chunk: Vec<u8> = s[src_off..src_off + len].to_vec();
    let mut r = into_rc(dest);
    let d = make_mut(&mut r, new_size.saturating_sub(dsz));
    if d.len() < new_size {
        d.resize(new_size, 0);
    }
    d[dest_off..dest_off + len].copy_from_slice(&chunk);
    from_rc(r)
}
