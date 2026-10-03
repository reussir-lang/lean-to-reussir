//! Releasing containers without recursion: arrays (`RVec`), references
//! (`LRef`) and thunk/task cells (`LCell`).
//!
//! Native Lean frees an object iteratively (`lean_dec_ref_cold`): the
//! children whose count drops to zero go onto a stack of objects to free,
//! popped last first. Reussir's drop glue does the same with the local
//! patch 0014: a record member it frees is pushed on a stack of pending
//! work per thread (`reussir_rt::drop`), which the outermost drop empties.
//! A record releases a container field through the container's Rust `Drop`
//! (the opaque type's drop hook), which releases the elements, records
//! again: a tree whose children are in arrays, a chain of thunks.
//!
//! So the containers of the prelude are this module's types, with a `Drop`
//! that frees their last reference through that same stack: one worklist
//! per thread for records, containers and leaves. A container freed while
//! another free runs (from an element's release, or from a record's glue)
//! is pushed instead of freed; the outermost free, glue or container, pops
//! the stack until it is empty. An array is emptied from its last element:
//! each popped element is released, and whatever that release pushes is
//! done before the next element. Releases of leaves (file handles,
//! promises: releases that can be observed) reached while a free runs are
//! pushed too (`active`/`defer`, used by `fs` and `task`). So the order of
//! observable releases is Lean's: the last element first, a nested array's
//! elements before the elements that precede it, a record's last field
//! first. Except at the top of a free that starts at a record that user
//! code drops (a list, tree or structure of handles dropped by itself):
//! Reussir releases that first cell's fields inline, in field order, each
//! completely (in Lean's order within it) before the next, so a list's head
//! handle is closed first. Natively that depends on where the value is
//! dropped (plan §10).
//!
//! The types are `#[repr(transparent)]` over Reussir's own
//! (`reussir_rt::collections::vec::Vec`, `reussir_rt::rc::Rc`), so the FFI
//! contract (an rc pointer whose count is the `u32` at its address) and
//! every other use are unchanged; they dereference to them.

use std::mem::ManuallyDrop;
use std::ops::{Deref, DerefMut};

/// One unit of pending work: `step(p)` does part of it and answers whether
/// it is finished (then the entry is removed).
type Step = unsafe fn(usize) -> bool;

/// Whether a free is running on this thread (a release now is pushed).
#[inline(always)]
pub fn active() -> bool {
    reussir_rt::drop::active()
}

/// Push work for the running free (see `active`).
pub fn defer(p: usize, step: Step) {
    reussir_rt::drop::defer_step(p, step);
}

/// Run `step` on `p` until it is finished, and everything it pushes; or,
/// inside a running free, push it. When the free is over, the dependents of
/// the promises it resolved are walked (`task::resolve`).
#[inline(never)]
pub fn run(p: usize, step: Step) {
    reussir_rt::drop::run_step(p, step);
    if !active() {
        crate::task::run_later_walks();
    }
}

#[inline(always)]
fn count(p: usize) -> u32 {
    unsafe { *(p as *const u32) }
}

/// An array or reference cell: Reussir's copy-on-write vector.
#[repr(transparent)]
pub struct Vec<T: Clone>(ManuallyDrop<reussir_rt::collections::vec::Vec<T>>);

impl<T: Clone> Vec<T> {
    #[inline(always)]
    pub fn from_inner(v: reussir_rt::collections::vec::Vec<T>) -> Self {
        Vec(ManuallyDrop::new(v))
    }
}

impl<T: Clone> Clone for Vec<T> {
    #[inline(always)]
    fn clone(&self) -> Self {
        Vec(ManuallyDrop::new((*self.0).clone()))
    }
}

impl<T: Clone> Deref for Vec<T> {
    type Target = reussir_rt::collections::vec::Vec<T>;
    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: Clone> DerefMut for Vec<T> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T: Clone> Drop for Vec<T> {
    #[inline(always)]
    fn drop(&mut self) {
        let p = unsafe { *(self as *const Self as *const usize) };
        let c = count(p);
        if c > 1 {
            // An array a conversion built is also held by the origin table
            // (`crate::origin`) until the program drops it.
            if c == 2 && crate::origin::release_shared(p) {
                return;
            }
            unsafe { *(p as *mut u32) = c - 1 };
        } else {
            free_vec::<T>(p);
        }
    }
}

/// Free the box of a vector whose last reference the caller gives up (the
/// `Rc<std::vec::Vec<T>>` at `p`, count 1).
#[cold]
#[inline(never)]
pub fn free_vec<T: Clone>(p: usize) {
    if !std::mem::needs_drop::<T>() {
        unsafe { drop(std::mem::transmute::<usize, reussir_rt::rc::Rc<std::vec::Vec<T>>>(p)) };
        return;
    }
    // Outside a free, `run` would release the elements now, from the last
    // one: those whose release only decrements (shared ones: the old
    // version of an array that was copied for an update) are released here
    // first, which is the same. If all are, the box is freed without the
    // stack; else the stack's work goes on from the first element whose
    // release frees it. Inside a free the array is only pushed, and its
    // elements are released when it is popped, after the work pushed before
    // it (a later field of the record being freed may hold one of them).
    if !active() {
        let mut r = ManuallyDrop::new(unsafe { std::mem::transmute::<usize, reussir_rt::rc::Rc<std::vec::Vec<T>>>(p) });
        if unsafe { T::release_shared_from_end(r.data_mut()) } {
            unsafe { ManuallyDrop::drop(&mut r) };
            return;
        }
    }
    run(p, step_vec::<T>);
}

/// Release the elements of the vector at `p` from the last one, until one
/// of them pushes work (done first) or none is left (then free the box).
unsafe fn step_vec<T: Clone>(p: usize) -> bool {
    let depth = reussir_rt::drop::depth();
    let mut r = ManuallyDrop::new(std::mem::transmute::<usize, reussir_rt::rc::Rc<std::vec::Vec<T>>>(p));
    if !T::release_from_end(r.data_mut(), depth) {
        return false;
    }
    ManuallyDrop::drop(&mut r);
    true
}

/// Releasing the elements of a vector being freed (`step_vec`).
trait ReleaseElems: Sized {
    /// Release elements from the last one until `v` is empty (`true`) or a
    /// release pushed work, which is done first (`false`; the elements left
    /// stay in `v`). `depth` is the stack's depth before.
    unsafe fn release_from_end(v: &mut std::vec::Vec<Self>, depth: usize) -> bool;
    /// Release elements from the last one while their release frees
    /// nothing; answers whether `v` is then empty. (For element types
    /// whose releases cannot be told apart, none: `v` stays as it is.)
    unsafe fn release_shared_from_end(v: &mut std::vec::Vec<Self>) -> bool;
}

#[inline(always)]
unsafe fn release_from_end_each<T>(v: &mut std::vec::Vec<T>, depth: usize) -> bool {
    while let Some(x) = v.pop() {
        drop(x);
        if v.is_empty() {
            break;
        }
        if reussir_rt::drop::depth() != depth {
            return false;
        }
    }
    true
}

impl<T> ReleaseElems for T {
    #[inline(always)]
    default unsafe fn release_from_end(v: &mut std::vec::Vec<T>, depth: usize) -> bool {
        release_from_end_each(v, depth)
    }
    #[inline(always)]
    default unsafe fn release_shared_from_end(v: &mut std::vec::Vec<T>) -> bool {
        v.is_empty()
    }
}

/// A Reussir record (`Bridge<Inner>`, see `array::ExtendCloned`): its
/// `Drop` is the compiler-emitted `<record>_ffi_release`, an out-of-line
/// call per element, which decrements the 32-bit count at offset 0 (not
/// stored for an immediate, whose top byte is a tag under the aarch64
/// encoding of nullary variants) and frees the box when the count was 1.
/// Here a shared element is decremented inline, as `lean_del` does
/// natively, and an immediate is skipped (its release changes nothing:
/// Reussir never frees one, local patch 0006); only an element whose count
/// is 1 goes through `<record>_ffi_release`, which frees it, so the order
/// of releases and the stack's work are as with the generic loop.
impl<X> ReleaseElems for reussir_rt::bridge::Bridge<X> {
    #[inline(always)]
    unsafe fn release_from_end(v: &mut std::vec::Vec<Self>, depth: usize) -> bool {
        if !(cfg!(target_arch = "aarch64") && std::mem::size_of::<Self>() == 8) {
            return release_from_end_each(v, depth);
        }
        let mut n = v.len();
        while n > 0 {
            let p = *(v.as_ptr().add(n - 1) as *const usize);
            if p >> 56 != 0 {
                n -= 1;
                v.set_len(n);
                continue;
            }
            let c = *(p as *const u32);
            if c != 1 {
                *(p as *mut u32) = c.wrapping_sub(1);
                n -= 1;
                v.set_len(n);
                continue;
            }
            n -= 1;
            let x = std::ptr::read(v.as_ptr().add(n));
            v.set_len(n);
            drop(x);
            if n == 0 {
                break;
            }
            if reussir_rt::drop::depth() != depth {
                return false;
            }
        }
        true
    }
    #[inline(always)]
    unsafe fn release_shared_from_end(v: &mut std::vec::Vec<Self>) -> bool {
        if !(cfg!(target_arch = "aarch64") && std::mem::size_of::<Self>() == 8) {
            return v.is_empty();
        }
        let mut n = v.len();
        while n > 0 {
            let p = *(v.as_ptr().add(n - 1) as *const usize);
            if p >> 56 == 0 {
                let c = *(p as *const u32);
                if c == 1 {
                    return false;
                }
                *(p as *mut u32) = c.wrapping_sub(1);
            }
            n -= 1;
            v.set_len(n);
        }
        true
    }
}

/// A thunk or task cell: Reussir's `Rc` around the state.
#[repr(transparent)]
pub struct Cell<T>(ManuallyDrop<reussir_rt::rc::Rc<T>>);

impl<T> Cell<T> {
    #[inline(always)]
    pub fn from_inner(c: reussir_rt::rc::Rc<T>) -> Self {
        Cell(ManuallyDrop::new(c))
    }
}

impl<T> Clone for Cell<T> {
    #[inline(always)]
    fn clone(&self) -> Self {
        Cell(ManuallyDrop::new((*self.0).clone()))
    }
}

impl<T> Deref for Cell<T> {
    type Target = reussir_rt::rc::Rc<T>;
    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for Cell<T> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T> Drop for Cell<T> {
    #[inline(always)]
    fn drop(&mut self) {
        let p = unsafe { *(self as *const Self as *const usize) };
        let c = count(p);
        if c > 1 {
            unsafe { *(p as *mut u32) = c - 1 };
        } else {
            free_cell::<T>(p);
        }
    }
}

#[cold]
#[inline(never)]
fn free_cell<T>(p: usize) {
    run(p, step_cell::<T>);
}

/// Free the cell at `p` (count 1), then release its value.
unsafe fn step_cell<T>(p: usize) -> bool {
    let v = crate::alloc::rc_into_inner(std::mem::transmute::<usize, reussir_rt::rc::Rc<T>>(p));
    drop(v);
    true
}
