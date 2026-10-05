//! Arrays of `Nat` / `Int` with one word per element, like Lean's arrays of
//! boxed scalars, in one allocation.
//!
//! Each element is the `Nat`'s or `Int`'s own word (`crate::nat`):
//!
//! - odd words are small values: `lean_box` of a `Nat` below 2^63 or of an
//!   `Int` in the `int32` range;
//! - even words are owned `LBig` handles (the raw block pointer), for all
//!   other values.
//!
//! The Reussir-visible type is `TagVec`, a `#[repr(transparent)]` pointer to
//! one allocation laid out like Lean's array object (the same 24-byte
//! header):
//!
//! ```text
//!   0: count: u32, (padding)     the reference count Reussir's `rc.inc` bumps
//!   8: len: usize
//!  16: cap: usize
//!  24: words: [u64; cap]
//! ```
//!
//! The FFI contract for an opaque type (an rc pointer whose `u32` count is
//! at its address; `rc.dec` calls the type's drop hook, which drops the
//! Rust value) is all Reussir relies on, so `TagVec`'s own `Clone` and
//! `Drop` do the counting: the last reference releases the big elements and
//! frees the block (`mi_free`). Like every array it is copy-on-write:
//! updated in place when unique.

use crate::big::LBig;
use std::ffi::c_void;

extern "C" {
    fn mi_malloc(size: usize) -> *mut c_void;
    fn mi_realloc(p: *mut c_void, size: usize) -> *mut c_void;
    fn mi_free(p: *mut c_void);
    fn mi_good_size(size: usize) -> usize;
}

#[repr(C)]
struct Obj {
    count: u32,
    _pad: u32,
    len: usize,
    cap: usize,
}

const HDR: usize = std::mem::size_of::<Obj>();

/// A tag vector handle (`LNatArr`, `LIntArr`): owns one reference.
///
/// Safety argument for the raw block: every `TagVec` points at a live block
/// from `alloc` or `grow` (`mi_malloc`/`mi_realloc`, 8-aligned: Reussir
/// builds mimalloc with `MI_MAX_ALIGN_SIZE=8`, and `Obj` and the words need
/// 8) of `HDR + 8 * cap` bytes or more, whose first `len <= cap` words are
/// initialized; the block is freed only by the reference that finds the
/// count at 1, and moved (`grow`) only through a unique handle, which is
/// then replaced by the result.
#[repr(transparent)]
pub struct TagVec(*mut Obj);

pub type LTagVec = TagVec;

impl TagVec {
    #[inline(always)]
    pub fn is_unique(&self) -> bool {
        unsafe { (*self.0).count == 1 }
    }
}

impl Clone for TagVec {
    #[inline(always)]
    fn clone(&self) -> Self {
        unsafe { (*self.0).count += 1 };
        TagVec(self.0)
    }
}

impl Drop for TagVec {
    /// A shared handle is a decrement; the last reference is freed out of
    /// line (keeps the textures that read an array small enough to inline).
    #[inline(always)]
    fn drop(&mut self) {
        let o = self.0;
        unsafe {
            let c = (*o).count;
            if c == 1 {
                free(o)
            } else {
                (*o).count = c - 1;
            }
        }
    }
}

impl crate::Release for TagVec {
    #[inline(always)]
    fn release(self) {
        drop(self)
    }
}

/// Free a block whose last reference went: release the big elements, then
/// the block.
#[cold]
#[inline(never)]
extern "C" fn free(o: *mut Obj) {
    unsafe {
        for w in std::slice::from_raw_parts(words(o), (*o).len) {
            if !is_small(*w) {
                drop(std::mem::transmute::<usize, LBig>(*w as usize));
            }
        }
        mi_free(o as *mut c_void);
    }
}

#[inline(always)]
fn is_small(w: u64) -> bool {
    w & 1 == 1
}

#[inline(always)]
fn big_to_word(b: LBig) -> u64 {
    // `LBig` is a `#[repr(transparent)]` raw pointer.
    unsafe { std::mem::transmute::<LBig, usize>(b) as u64 }
}

/// Borrow the big handle stored in a word.
#[inline(always)]
fn word_as_big(w: &u64) -> &LBig {
    unsafe { &*(w as *const u64 as *const LBig) }
}

#[inline(always)]
fn obj(a: &LTagVec) -> *mut Obj {
    a.0
}

#[inline(always)]
unsafe fn words(o: *mut Obj) -> *mut u64 {
    (o as *mut u8).add(HDR) as *mut u64
}

#[inline(always)]
fn slice(a: &LTagVec) -> &[u64] {
    let o = obj(a);
    unsafe { std::slice::from_raw_parts(words(o), (*o).len) }
}

#[cold]
#[inline(never)]
fn oom() -> ! {
    crate::lean_internal_panic(lean_runtime::semantics::panic::InternalPanic::OutOfMemory)
}

#[inline(always)]
fn bytes_for(cap: usize) -> usize {
    cap.checked_mul(8).and_then(|b| b.checked_add(HDR)).unwrap_or_else(|| oom())
}

/// A fresh unique object with room for `cap` words and no elements.
#[inline(always)]
fn alloc(cap: usize) -> LTagVec {
    unsafe {
        let o = mi_malloc(bytes_for(cap)) as *mut Obj;
        if o.is_null() {
            oom();
        }
        std::ptr::write(o, Obj { count: 1, _pad: 0, len: 0, cap });
        TagVec(o)
    }
}

/// Grow a unique object to room for at least `need` words (at least
/// doubling). The capacity is all of the block: mimalloc's size classes
/// for small blocks (`mi_good_size`), and powers of two beyond 4 KiB, as a
/// vector buffer's would be. With the header added to a power of two,
/// large blocks fell just past mimalloc's size steps, and growing a
/// 10M-element array peaked 35 MB higher (realloc copies a block's whole
/// usable size).
#[cold]
#[inline(never)]
extern "C" fn grow(a: LTagVec, need: usize) -> LTagVec {
    debug_assert!(a.is_unique());
    let o = obj(&a);
    // The block moves: the unique handle is given up for the result.
    std::mem::forget(a);
    unsafe {
        let want = need.max((*o).cap.saturating_mul(2)).max(4);
        let b = bytes_for(want);
        let bytes = if b > 4096 { b.checked_next_power_of_two().unwrap_or(b) } else { mi_good_size(b) };
        // `bytes >= b = HDR + 8 * want`, so the new capacity is at least
        // `want`; realloc keeps the header and the `len` words.
        let n = mi_realloc(o as *mut c_void, bytes) as *mut Obj;
        if n.is_null() {
            oom();
        }
        (*n).cap = (bytes - HDR) / 8;
        TagVec(n)
    }
}

/// A private copy of a shared vector with room for `extra` more words
/// (keeping at least the capacity, as `lean_copy_expand_array` does),
/// releasing the shared one.
#[cold]
#[inline(never)]
extern "C" fn copy_shared(a: LTagVec, extra: usize) -> LTagVec {
    let src = slice(&a);
    let cap = (src.len() + extra).max(unsafe { (*obj(&a)).cap });
    let c = alloc(cap);
    unsafe { copy_words(src, words(obj(&c))) };
    unsafe { (*obj(&c)).len = src.len() };
    drop(a);
    c
}

/// Unique access with room for `extra` more words, copying a shared vector
/// first.
#[inline(always)]
fn make_mut(a: &mut LTagVec, extra: usize) -> *mut Obj {
    // By value: the address of `a` (often a local of the Reussir caller once
    // this is inlined) must not escape, or tail calls are lost.
    if !a.is_unique() {
        unsafe { std::ptr::write(a, copy_shared(std::ptr::read(a), extra)) };
    } else if extra > 0 {
        let o = obj(a);
        let need = unsafe { (*o).len } + extra;
        if need > unsafe { (*o).cap } {
            unsafe { std::ptr::write(a, grow(std::ptr::read(a), need)) };
        }
    }
    obj(a)
}

/// Copy words to `dst`, taking a reference to every big element among them.
#[inline]
unsafe fn copy_words(ws: &[u64], dst: *mut u64) {
    for w in ws {
        if !is_small(*w) {
            std::mem::forget(word_as_big(w).clone());
        }
    }
    std::ptr::copy_nonoverlapping(ws.as_ptr(), dst, ws.len());
}

#[cold]
#[inline(never)]
extern "C" fn index_bug(i: u64, n: usize) -> ! {
    crate::internal_panic(&format!("array index {} out of bounds {} (runtime invariant)", i, n))
}

#[cold]
#[inline(never)]
extern "C" fn drop_word(w: u64) {
    if !is_small(w) {
        drop(unsafe { std::mem::transmute::<usize, LBig>(w as usize) });
    }
}

#[inline(never)]
pub fn empty() -> LTagVec {
    alloc(0)
}

/// `Array.mkEmpty n`: Lean's allocation checks for a capacity
/// (`array::check_capacity`), then the capacity asked for (natively
/// reserved too; untouched pages cost no memory).
#[inline(never)]
pub fn with_capacity(n: u64) -> LTagVec {
    crate::array::check_capacity(n, 8);
    alloc(n as usize)
}

/// `n` copies of a word that owns its reference (a big word: one reference
/// per copy, the word's own released when `n` is 0).
#[inline(never)]
pub fn replicate_word(n: u64, w: u64) -> LTagVec {
    if !is_small(w) {
        let b = unsafe { std::mem::transmute::<usize, LBig>(w as usize) };
        return replicate_big(n, b);
    }
    crate::array::check_alloc(n, 8);
    let a = alloc(n as usize);
    let o = obj(&a);
    unsafe {
        std::slice::from_raw_parts_mut(words(o), n as usize).fill(w);
        (*o).len = n as usize;
    }
    a
}

/// `n` references to one big value.
#[inline(never)]
pub fn replicate_big(n: u64, b: LBig) -> LTagVec {
    crate::array::check_alloc(n, 8);
    let a = alloc(n as usize);
    let o = obj(&a);
    unsafe {
        for i in 0..n as usize {
            *words(o).add(i) = big_to_word(b.clone());
        }
        (*o).len = n as usize;
    }
    a
}

#[inline(always)]
pub fn size(a: &LTagVec) -> u64 {
    unsafe { (*obj(a)).len as u64 }
}

/// The raw word at `i` (in bounds).
#[inline(always)]
pub fn word(a: &LTagVec, i: u64) -> u64 {
    let o = obj(a);
    let n = unsafe { (*o).len };
    if (i as usize) < n {
        unsafe { *words(o).add(i as usize) }
    } else {
        index_bug(i, n)
    }
}

/// The big value at `i` (the word there must be even).
#[inline(always)]
pub fn big(a: &LTagVec, i: u64) -> LBig {
    word_as_big(&slice(a)[i as usize]).clone()
}

/// The first step of a read of a tag vector (the prelude's
/// `l2r_natarr_give`, `intarr` too): the caller's handle is given up for a
/// view, as `array::give`.
#[inline(always)]
pub fn give(a: LTagVec) -> u64 {
    let o = obj(&a);
    std::mem::forget(a);
    unsafe {
        let c = (*o).count;
        if c != 1 {
            (*o).count = c - 1;
            o as u64 | 1
        } else {
            o as u64
        }
    }
}

/// The size of the tag vector of a view (`give`).
///
/// # Safety
/// `p` is a view from `give` that neither `view_take` nor `view_end` has
/// ended.
#[inline(always)]
pub unsafe fn view_size(p: u64) -> u64 {
    unsafe { (*((p & !1) as *mut Obj)).len as u64 }
}

/// The word at `i` of the tag vector of a view (`give`), which ends here
/// (`array::view_take`). A big word comes back owning one reference to its
/// value (so it outlives the array), to be turned back into the handle
/// with `big_of_owned_word`. A small word of a shared array is the whole
/// read; a big word and the last reference go to one out-of-line call,
/// `view_take_slow`.
///
/// # Safety
/// `p` is a view from `give` that neither `view_take` nor `view_end` has
/// ended, and `i` is below its size.
#[inline(always)]
pub unsafe fn view_take(p: u64, i: u64) -> u64 {
    let o = (p & !1) as *mut Obj;
    unsafe {
        debug_assert!((i as usize) < (*o).len);
        let w = *words(o).add(i as usize);
        if ((p & 1) != 0) & is_small(w) {
            w
        } else {
            view_take_slow(p, w)
        }
    }
}

/// `view_take` for a big word or the last reference: the word's big value
/// gets a reference (the array still holds it, through another reference
/// or through this view until the free below), and the last reference
/// frees the block, releasing its big elements (`free`).
#[cold]
#[inline(never)]
extern "C" fn view_take_slow(p: u64, w: u64) -> u64 {
    if !is_small(w) {
        std::mem::forget(word_as_big(&w).clone());
    }
    if (p & 1) == 0 {
        free((p & !1) as *mut Obj);
    }
    w
}

/// The end of a view without a read (`get!` out of bounds): the last
/// reference frees the block.
///
/// # Safety
/// `p` is a view from `give` that neither `view_take` nor `view_end` has
/// ended.
#[inline(always)]
pub unsafe fn view_end(p: u64) {
    if (p & 1) == 0 {
        free((p & !1) as *mut Obj);
    }
}

/// The big handle owned by a word from `view_take`.
#[inline(always)]
pub fn big_of_owned_word(w: u64) -> LBig {
    debug_assert!(!is_small(w));
    unsafe { std::mem::transmute::<usize, LBig>(w as usize) }
}

#[inline(always)]
fn set_raw(mut a: LTagVec, i: u64, w: u64) -> LTagVec {
    let o = make_mut(&mut a, 0);
    let n = unsafe { (*o).len };
    if (i as usize) >= n {
        index_bug(i, n);
    }
    let old = unsafe { std::ptr::replace(words(o).add(i as usize), w) };
    if !is_small(old) {
        drop_word(old);
    }
    a
}

/// Store a word at `i` (a big word's reference moves into the array).
#[inline(always)]
pub fn set_word(a: LTagVec, i: u64, w: u64) -> LTagVec {
    set_raw(a, i, w)
}

#[inline(always)]
pub fn set_big(a: LTagVec, i: u64, b: LBig) -> LTagVec {
    set_raw(a, i, big_to_word(b))
}

#[inline(always)]
fn push_raw(a: LTagVec, w: u64) -> LTagVec {
    if a.is_unique() {
        let o = obj(&a);
        unsafe {
            let n = (*o).len;
            if n < (*o).cap {
                *words(o).add(n) = w;
                (*o).len = n + 1;
                return a;
            }
        }
    }
    push_slow(a, w)
}

/// `push` when shared or full. A shared array is copied with the capacity
/// `lean_array_push` gives it (its own, unless that is below `2 * size + 1`:
/// then `(capacity + 1) * 2`), so a literal pushing onto a shared empty
/// array of capacity `k` allocates once, `k` words.
#[cold]
#[inline(never)]
extern "C" fn push_slow(mut a: LTagVec, w: u64) -> LTagVec {
    let n = slice(&a).len();
    let cap = unsafe { (*obj(&a)).cap };
    let want = if cap < 2 * n + 1 { (cap + 1) * 2 } else { cap };
    let o = if a.is_unique() {
        make_mut(&mut a, n.max(4))
    } else {
        make_mut(&mut a, want.max(n + 1) - n)
    };
    unsafe {
        *words(o).add(n) = w;
        (*o).len = n + 1;
    }
    a
}

#[inline(always)]
pub fn push_word(a: LTagVec, w: u64) -> LTagVec {
    push_raw(a, w)
}

#[inline(always)]
pub fn push_big(a: LTagVec, b: LBig) -> LTagVec {
    push_raw(a, big_to_word(b))
}

#[inline(never)]
pub fn pop(mut a: LTagVec) -> LTagVec {
    if slice(&a).is_empty() {
        return a;
    }
    let o = make_mut(&mut a, 0);
    unsafe {
        let n = (*o).len - 1;
        (*o).len = n;
        drop_word(*words(o).add(n));
    }
    a
}

#[inline(always)]
pub fn swap(mut a: LTagVec, i: u64, j: u64) -> LTagVec {
    let n = slice(&a).len();
    if (i as usize) >= n || (j as usize) >= n {
        index_bug(i.max(j), n);
    }
    let o = make_mut(&mut a, 0);
    unsafe { std::ptr::swap(words(o).add(i as usize), words(o).add(j as usize)) };
    a
}

#[inline(never)]
pub fn append(a: LTagVec, b: LTagVec) -> LTagVec {
    let k = slice(&b).len();
    if k == 0 {
        drop(b);
        return a;
    }
    let mut a = a;
    let o = make_mut(&mut a, k);
    unsafe {
        let n = (*o).len;
        copy_words(slice(&b), words(o).add(n));
        (*o).len = n + k;
    }
    drop(b);
    a
}

#[inline(never)]
pub fn extract(a: LTagVec, start: u64, stop: u64) -> LTagVec {
    let v = slice(&a);
    let stop = (stop as usize).min(v.len());
    let start = (start as usize).min(stop);
    if start == 0 && stop == v.len() {
        return a;
    }
    let c = alloc(stop - start);
    unsafe {
        copy_words(&v[start..stop], words(obj(&c)));
        (*obj(&c)).len = stop - start;
    }
    drop(a);
    c
}

#[inline(never)]
pub fn truncate(mut a: LTagVec, n: u64) -> LTagVec {
    let len = slice(&a).len();
    if (n as usize) >= len {
        return a;
    }
    let o = make_mut(&mut a, 0);
    unsafe {
        (*o).len = n as usize;
        for i in n as usize..len {
            drop_word(*words(o).add(i));
        }
    }
    a
}

#[inline(never)]
pub fn reverse(mut a: LTagVec) -> LTagVec {
    let o = make_mut(&mut a, 0);
    unsafe { std::slice::from_raw_parts_mut(words(o), (*o).len).reverse() };
    a
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rc(b: &LBig) -> u32 {
        b.count()
    }

    fn count(a: &LTagVec) -> u32 {
        unsafe { (*obj(a)).count }
    }

    #[test]
    fn layout() {
        // Lean's array header: the count word, the size and the capacity.
        assert_eq!(HDR, 24);
        assert_eq!(std::mem::size_of::<TagVec>(), 8);
        assert_eq!(std::mem::offset_of!(Obj, count), 0);
    }

    #[test]
    fn handle_counts() {
        let a = push_word(empty(), 3);
        assert_eq!(count(&a), 1);
        let b = a.clone();
        assert_eq!(count(&a), 2);
        assert!(!a.is_unique());
        crate::rc_release(b);
        assert_eq!(count(&a), 1);
        assert!(a.is_unique());
        // A unique array grows in place (realloc) and keeps its words.
        let mut a = a;
        for i in 0..5000u64 {
            a = push_word(a, (i << 1) | 1);
        }
        assert_eq!(size(&a), 5001);
        assert_eq!(word(&a, 0), 3);
        assert_eq!(word(&a, 5000), (4999 << 1) | 1);
        assert!(unsafe { (*obj(&a)).cap } >= 5001);
        assert_eq!(count(&a), 1);
        // An update of a shared array copies it; the original keeps its
        // count and contents.
        let keep = a.clone();
        let c = set_word(a, 0, 5);
        assert_eq!(count(&keep), 1);
        assert_eq!(count(&c), 1);
        assert_eq!(word(&keep, 0), 3);
        assert_eq!(word(&c, 0), 5);
    }

    #[test]
    fn big_element_counts() {
        let b = crate::big::of_limbs2(1, 1);
        let a = push_big(push_word(empty(), 7), b.clone());
        assert_eq!(rc(&b), 2);
        let a2 = a.clone(); // shared array
        let a3 = set_word(a2, 1, 9); // copy-on-write: the copy takes a reference, then drops it
        assert_eq!(rc(&b), 2);
        assert_eq!(word(&a3, 1), 9);
        let e = extract(a.clone(), 1, 2);
        assert_eq!(rc(&b), 3);
        drop(e);
        let ap = append(a.clone(), a.clone());
        assert_eq!(rc(&b), 4);
        assert_eq!(size(&ap), 4);
        drop(ap);
        assert_eq!(rc(&b), 2);
        let t = truncate(a.clone(), 1);
        assert_eq!(size(&t), 1);
        assert_eq!(rc(&b), 2);
        drop(t);
        drop(a);
        drop(a3);
        assert_eq!(rc(&b), 1);
        let r = replicate_big(3, b.clone());
        assert_eq!(rc(&b), 4);
        let r = pop(r);
        assert_eq!(rc(&b), 3);
        let r = set_word(r, 0, 1);
        assert_eq!(rc(&b), 2);
        assert_eq!(crate::big::limbs(&big(&r, 1)), crate::big::limbs(&b));
        drop(r);
        assert_eq!(rc(&b), 1);
    }

    #[test]
    fn views() {
        let b = crate::big::of_limbs2(1, 1);
        let a = push_big(push_word(empty(), 7), b.clone());
        assert_eq!(rc(&b), 2);
        // A shared array: `give` decrements now; a small word is the whole
        // read, a big word comes back owning a reference.
        let p = give(a.clone());
        assert_eq!(p & 1, 1);
        assert_eq!(count(&a), 1);
        assert_eq!(unsafe { view_size(p) }, 2);
        assert_eq!(unsafe { view_take(p, 0) }, 7);
        let p = give(a.clone());
        let w = unsafe { view_take(p, 1) };
        assert_eq!(rc(&b), 3);
        drop(big_of_owned_word(w));
        assert_eq!(rc(&b), 2);
        assert_eq!(count(&a), 1);
        // A shared view ended without a read changes nothing more.
        unsafe { view_end(give(a.clone())) };
        assert_eq!(count(&a), 1);
        // The last reference: the read frees the block (releasing its big
        // element), the big word it returns keeps its own reference.
        let a2 = a.clone();
        let p = give(a);
        let w = unsafe { view_take(p, 1) };
        assert_eq!(rc(&b), 3);
        let p = give(a2);
        assert_eq!(p & 1, 0);
        assert_eq!(unsafe { view_take(p, 0) }, 7);
        assert_eq!(rc(&b), 2);
        drop(big_of_owned_word(w));
        assert_eq!(rc(&b), 1);
        // `view_end` of the last reference frees the block.
        let c = push_big(empty(), b.clone());
        assert_eq!(rc(&b), 2);
        unsafe { view_end(give(c)) };
        assert_eq!(rc(&b), 1);
    }

    #[test]
    fn growth_and_sharing() {
        let b = crate::big::of_limbs2(5, 5);
        let mut a = empty();
        for i in 0..1000u64 {
            a = if i % 100 == 0 { push_big(a, b.clone()) } else { push_word(a, (i << 1) | 1) };
        }
        assert_eq!(size(&a), 1000);
        assert_eq!(rc(&b), 11);
        for i in 0..1000u64 {
            if i % 100 != 0 {
                assert_eq!(word(&a, i), (i << 1) | 1);
            }
        }
        // A shared empty array with capacity (a literal's closed term):
        // the first push copies it once, keeping the capacity.
        let lit = with_capacity(4);
        let x = push_word(lit.clone(), 3);
        assert_eq!(unsafe { (*obj(&x)).cap }, 4);
        let x = push_word(push_word(push_word(x, 5), 7), 9);
        assert_eq!(slice(&x), &[3, 5, 7, 9]);
        assert_eq!(size(&lit), 0);
        let s = swap(reverse(a.clone()), 0, 1);
        assert_eq!(rc(&b), 21);
        drop(s);
        drop(a);
        assert_eq!(rc(&b), 1);
    }
}
