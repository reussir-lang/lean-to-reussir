//! Arrays of `Nat` / `Int` with one word per element, like Lean's arrays of
//! boxed scalars.
//!
//! `Nat` and `Int` are Reussir `[value]` enums, which cannot be stored in a
//! Rust vector; storing them boxed costs an allocation per element update.
//! A `TagVec` stores each element as a tagged word instead:
//!
//! - odd words are small values: `(v << 1) | 1` (the Reussir side decides
//!   the range and the signedness: `Nat` below 2^63, `Int` in [-2^62, 2^62));
//! - even words are owned `LBig` handles (the raw `Rc` pointer), for all
//!   other values.
//!
//! The Reussir-visible type is `Rc<Box<dyn Any>>` (spellable with std and
//! reussir_rt only, as opaque FFI types must be); the `Box` holds a
//! `TagVec`, whose `Clone`/`Drop` maintain the big elements' counts. Like
//! every array it is copy-on-write: updated in place when unique.

use crate::alloc::{box_new, rc_new, reserve, vec_from_slice, vec_with_capacity};
use crate::big::LBig;
use reussir_rt::rc::Rc;
use std::any::Any;

pub type LTagVec = Rc<Box<dyn Any>>;

pub struct TagVec {
    w: Vec<u64>,
}

#[inline(always)]
fn is_small(w: u64) -> bool {
    w & 1 == 1
}

#[inline(always)]
fn big_to_word(b: LBig) -> u64 {
    // `Rc` is a `#[repr(transparent)]` raw pointer.
    unsafe { std::mem::transmute::<LBig, usize>(b) as u64 }
}

/// Borrow the big handle stored in a word.
#[inline(always)]
fn word_as_big(w: &u64) -> &LBig {
    unsafe { &*(w as *const u64 as *const LBig) }
}

impl Clone for TagVec {
    fn clone(&self) -> Self {
        TagVec { w: copy_words(&self.w) }
    }
}

impl Drop for TagVec {
    fn drop(&mut self) {
        for w in &self.w {
            if !is_small(*w) {
                drop(unsafe { std::mem::transmute::<usize, LBig>(*w as usize) });
            }
        }
    }
}

#[inline(always)]
fn tv(a: &LTagVec) -> &TagVec {
    // Only this module creates these objects, always holding a `TagVec`.
    unsafe { &*(&***a as *const dyn Any as *const TagVec) }
}

#[inline(always)]
fn tv_mut(a: &mut LTagVec) -> &mut TagVec {
    unsafe { &mut *(&mut **a.data_mut() as *mut dyn Any as *mut TagVec) }
}

fn mk(w: Vec<u64>) -> LTagVec {
    rc_new(box_new(TagVec { w }) as Box<dyn Any>)
}

/// Unique access, copying a shared vector first.
#[inline(always)]
fn make_mut(a: &mut LTagVec) -> &mut TagVec {
    if !a.is_unique() {
        copy_shared(a);
    }
    tv_mut(a)
}

#[cold]
#[inline(never)]
fn copy_shared(a: &mut LTagVec) {
    let c = tv(a).clone();
    *a = rc_new(box_new(c) as Box<dyn Any>);
}

#[cold]
#[inline(never)]
fn index_bug(i: u64, n: usize) -> ! {
    crate::internal_panic(&format!("array index {} out of bounds {} (runtime invariant)", i, n))
}

#[cold]
#[inline(never)]
fn drop_word(w: u64) {
    if !is_small(w) {
        drop(unsafe { std::mem::transmute::<usize, LBig>(w as usize) });
    }
}

#[inline(never)]
pub fn empty() -> LTagVec {
    mk(Vec::new())
}

#[inline(never)]
pub fn with_capacity(n: u64) -> LTagVec {
    crate::array::check_alloc(n, 8);
    mk(vec_with_capacity(n.min(crate::array::CAPACITY_CAP) as usize))
}

/// `n` copies of a small (odd) word.
#[inline(never)]
pub fn replicate_word(n: u64, w: u64) -> LTagVec {
    {
        crate::array::check_alloc(n, 8);
        let mut v = vec_with_capacity(n as usize);
        v.resize(n as usize, w);
        mk(v)
    }
}

/// `n` references to one big value.
#[inline(never)]
pub fn replicate_big(n: u64, b: LBig) -> LTagVec {
    crate::array::check_alloc(n, 8);
    let mut v = vec_with_capacity(n as usize);
    for _ in 0..n {
        v.push(big_to_word(b.clone()));
    }
    mk(v)
}

#[inline(always)]
pub fn size(a: &LTagVec) -> u64 {
    tv(a).w.len() as u64
}

/// The raw word at `i` (in bounds).
#[inline(always)]
pub fn word(a: &LTagVec, i: u64) -> u64 {
    match tv(a).w.get(i as usize) {
        Some(w) => *w,
        None => index_bug(i, tv(a).w.len()),
    }
}

/// The big value at `i` (the word there must be even).
#[inline(always)]
pub fn big(a: &LTagVec, i: u64) -> LBig {
    word_as_big(&tv(a).w[i as usize]).clone()
}

#[inline(always)]
fn set_raw(mut a: LTagVec, i: u64, w: u64) -> LTagVec {
    let v = make_mut(&mut a);
    match v.w.get_mut(i as usize) {
        Some(slot) => {
            let old = std::mem::replace(slot, w);
            if !is_small(old) {
                drop_word(old);
            }
        }
        None => index_bug(i, v.w.len()),
    }
    a
}

/// Store a small (odd) word at `i`.
#[inline(always)]
pub fn set_word(a: LTagVec, i: u64, w: u64) -> LTagVec {
    set_raw(a, i, w)
}

#[inline(always)]
pub fn set_big(a: LTagVec, i: u64, b: LBig) -> LTagVec {
    set_raw(a, i, big_to_word(b))
}

#[inline(always)]
fn push_raw(mut a: LTagVec, w: u64) -> LTagVec {
    if a.is_unique() {
        let v = tv_mut(&mut a);
        if v.w.len() < v.w.capacity() {
            v.w.push(w);
            return a;
        }
    }
    push_slow(a, w)
}

#[cold]
#[inline(never)]
fn push_slow(mut a: LTagVec, w: u64) -> LTagVec {
    let v = make_mut(&mut a);
    let n = v.w.len();
    reserve(&mut v.w, n.max(4));
    v.w.push(w);
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
    if tv(&a).w.is_empty() {
        return a;
    }
    let v = make_mut(&mut a);
    if let Some(w) = v.w.pop() {
        drop_word(w);
    }
    a
}

#[inline(always)]
pub fn swap(mut a: LTagVec, i: u64, j: u64) -> LTagVec {
    let n = tv(&a).w.len();
    if (i as usize) >= n || (j as usize) >= n {
        index_bug(i.max(j), n);
    }
    make_mut(&mut a).w.swap(i as usize, j as usize);
    a
}

/// Copy words, taking a reference to every big element among them.
fn copy_words(ws: &[u64]) -> Vec<u64> {
    for w in ws {
        if !is_small(*w) {
            std::mem::forget(word_as_big(w).clone());
        }
    }
    vec_from_slice(ws, 0)
}

#[inline(never)]
pub fn append(a: LTagVec, b: LTagVec) -> LTagVec {
    let mut a = a;
    let extra = copy_words(&tv(&b).w);
    make_mut(&mut a).w.extend_from_slice(&extra);
    a
}

#[inline(never)]
pub fn extract(a: LTagVec, start: u64, stop: u64) -> LTagVec {
    let v = &tv(&a).w;
    let stop = (stop as usize).min(v.len());
    let start = (start as usize).min(stop);
    if start == 0 && stop == v.len() {
        return a;
    }
    mk(copy_words(&v[start..stop]))
}

#[inline(never)]
pub fn truncate(mut a: LTagVec, n: u64) -> LTagVec {
    if (n as usize) >= tv(&a).w.len() {
        return a;
    }
    let v = make_mut(&mut a);
    for w in v.w.drain(n as usize..) {
        drop_word(w);
    }
    a
}

#[inline(never)]
pub fn reverse(mut a: LTagVec) -> LTagVec {
    make_mut(&mut a).w.reverse();
    a
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rc(b: &LBig) -> u32 {
        b.count_ref().get()
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
        assert_eq!(big(&r, 1).1, b.1);
        drop(r);
        assert_eq!(rc(&b), 1);
    }
}
