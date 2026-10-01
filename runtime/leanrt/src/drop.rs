//! Releasing containers without recursion: arrays (`RVec`), references
//! (`LRef`) and thunk/task cells (`LCell`).
//!
//! Native Lean frees an object iteratively (`lean_dec_ref_cold`): the
//! children whose count drops to zero go onto a stack of objects to free,
//! popped last first. Reussir's drop glue for records recurses (along the
//! cell's last chain member it loops, with the local patch 0013), and a
//! record releases a container field through the container's Rust `Drop`
//! (the opaque type's drop hook), which releases the elements, records
//! again: a tree whose children are in arrays, a chain of thunks, used one
//! stack frame or more per level and overflowed where native Lean does not.
//!
//! So the containers of the prelude are this module's types, with a `Drop`
//! that frees their last reference through one stack of pending work per
//! thread, as Lean does. A container freed while another free runs (from an
//! element's release, at any depth of record glue in between) is pushed
//! instead of freed; the outermost free pops the stack until it is empty.
//! An array is emptied from its last element: each popped element is
//! released, and whatever that release pushes is done before the next
//! element. So for leaves (file handles, promises: releases that can be
//! observed) the order is Lean's: the last element first, and a nested
//! array's elements before the elements that precede it. Releases of such
//! leaves reached through records during a free are pushed too
//! (`active`/`defer`, used by `fs` and `task`), so that a record's fields
//! come out last first, as natively; a release that starts at a record
//! outside any container free runs in Reussir's order (the record's fields
//! in order).
//!
//! The types are `#[repr(transparent)]` over Reussir's own
//! (`reussir_rt::collections::vec::Vec`, `reussir_rt::rc::Rc`), so the FFI
//! contract (an rc pointer whose count is the `u32` at its address) and
//! every other use are unchanged; they dereference to them.

use std::cell::{Cell as StdCell, RefCell};
use std::mem::ManuallyDrop;
use std::ops::{Deref, DerefMut};

/// One unit of pending work: `step(p)` does part of it and answers whether
/// it is finished (then the entry is removed).
type Step = unsafe fn(usize) -> bool;

thread_local! {
    static ACTIVE: StdCell<bool> = const { StdCell::new(false) };
    static WORK: RefCell<std::vec::Vec<(usize, Step)>> = const { RefCell::new(std::vec::Vec::new()) };
}

/// Whether a free is running on this thread (a release now is pushed).
#[inline(always)]
pub fn active() -> bool {
    ACTIVE.with(|a| a.get())
}

/// Push work for the running free (see `active`).
pub fn defer(p: usize, step: Step) {
    WORK.with(|w| w.borrow_mut().push((p, step)));
}

/// Run `step` on `p` until it is finished, and everything it pushes; or,
/// inside a running free, push it.
#[inline(never)]
pub fn run(p: usize, step: Step) {
    if active() {
        defer(p, step);
        return;
    }
    ACTIVE.with(|a| a.set(true));
    defer(p, step);
    loop {
        let top = WORK.with(|w| {
            let w = w.borrow();
            w.last().map(|&(p, s)| (w.len() - 1, p, s))
        });
        let Some((i, p, s)) = top else { break };
        if unsafe { s(p) } {
            WORK.with(|w| {
                w.borrow_mut().remove(i);
            });
        }
    }
    ACTIVE.with(|a| a.set(false));
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
    run(p, step_vec::<T>);
}

/// Release the elements of the vector at `p` from the last one, until one
/// of them pushes work (done first) or none is left (then free the box).
unsafe fn step_vec<T: Clone>(p: usize) -> bool {
    let depth = WORK.with(|w| w.borrow().len());
    let mut r = ManuallyDrop::new(std::mem::transmute::<usize, reussir_rt::rc::Rc<std::vec::Vec<T>>>(p));
    loop {
        let x = r.data_mut().pop();
        match x {
            Some(x) => {
                drop(x);
                if r.data_ref().is_empty() {
                    break;
                }
                if WORK.with(|w| w.borrow().len()) != depth {
                    return false;
                }
            }
            None => break,
        }
    }
    ManuallyDrop::drop(&mut r);
    true
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
