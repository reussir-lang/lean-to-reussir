//! Arrays: Reussir's copy-on-write `reussir_rt::collections::vec::Vec<T>`.
//!
//! That type is a `#[repr(transparent)]` wrapper over
//! `reussir_rt::rc::Rc<std::vec::Vec<T>>` (the FFI contract requires it), so
//! the runtime views it as the `Rc` directly to get slice access, `reserve`,
//! `truncate`, ... Every mutation goes through `make_mut`, which copies a
//! shared buffer first: arrays are values, updated in place only when
//! uniquely referenced, like Lean's.
//!
//! `ByteArray` and `FloatArray` are `RVec<u8>`/`RVec<f64>`; a `String`
//! (`Rc<Vec<u8>>`) has the same layout as `RVec<u8>`, which makes
//! `String.toUTF8`/`String.fromUTF8` free.

use reussir_rt::collections::vec::Vec as RVec;
use reussir_rt::rc::Rc;
use crate::alloc::{rc_new, reserve, vec_from_slice, vec_with_capacity};

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
fn drop_last<T>(r: Rc<Vec<T>>) {
    drop(r)
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
        copy_shared(v, extra);
    }
    let vec = unsafe { v.data_mut() };
    reserve(vec, extra);
    vec
}

/// Replace a shared array by a private copy (with room for `extra` more).
#[cold]
#[inline(never)]
fn copy_shared<T: Clone>(v: &mut Rc<Vec<T>>, extra: usize) {
    *v = rc_new(vec_from_slice(v, extra));
}

/// An index that the Lean-level proof (or the prelude's bounds check)
/// guarantees to be in range was not: a lean2rr/runtime bug.
#[cold]
#[inline(never)]
fn index_bug(i: u64, n: usize) -> ! {
    crate::internal_panic(&format!("array index {} out of bounds {} (runtime invariant)", i, n))
}

#[inline]
pub fn with_capacity<T: Clone>(n: usize) -> RVec<T> {
    from_rc(rc_new(vec_with_capacity(n)))
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

#[cold]
#[inline(never)]
fn push_slow<T: Clone>(mut r: Rc<Vec<T>>, x: T) -> RVec<T> {
    let n = r.len();
    make_mut(&mut r, n.max(4)).push(x);
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
fn set_slow<T: Clone>(mut r: Rc<Vec<T>>, i: u64, x: T) -> RVec<T> {
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
fn pop_slow<T: Clone>(mut r: Rc<Vec<T>>) -> RVec<T> {
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
fn swap_slow<T: Clone>(mut r: Rc<Vec<T>>, i: u64, j: u64) -> RVec<T> {
    make_mut(&mut r, 0).swap(i as usize, j as usize);
    from_rc(r)
}

/// `Array.replicate n x`.
#[inline(never)]
pub fn replicate<T: Clone>(n: u64, x: T) -> RVec<T> {
    {
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
    make_mut(&mut r, bs.len()).extend_from_slice(bs);
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
    from_rc(rc_new(vec_from_slice(&s[start..stop], 0)))
}

/// Reverse in place.
#[inline(never)]
pub fn reverse<T: Clone>(v: RVec<T>) -> RVec<T> {
    let mut r = into_rc(v);
    make_mut(&mut r, 0).reverse();
    from_rc(r)
}

// ---- byte arrays and strings share a layout -------------------------------

#[inline(always)]
pub fn bytes_of_string(s: crate::string::LStr) -> RVec<u8> {
    from_rc(s)
}

#[inline(always)]
pub fn string_of_bytes(b: RVec<u8>) -> crate::string::LStr {
    into_rc(b)
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
