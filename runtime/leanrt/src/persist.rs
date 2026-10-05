//! The walk of a constant's value for its tasks (lean2rr's `l2r_persist_T`,
//! translation plan §5.14). Native Lean marks a closed term persistent when
//! it is first evaluated (`lean_mark_persistent`): it visits every object
//! the value reaches once, with a stack of objects to visit, and waits for
//! each task. The generated walk is a loop over a work list; this module is
//! its set of visited cells, so that a value whose cells are shared (a DAG)
//! is walked in time linear in its number of cells, not of its paths.
//!
//! Natively waiting for a task only blocks: the term's tasks are run by the
//! workers in the order they were queued (by priority, then first in first
//! out), whatever order the walk waits for them in. lean-runtime's `wait`
//! does the same (it runs the awaited task only once a free worker would
//! start it, and the queue's heads start on contexts of their own
//! meanwhile), so the walk waits for each task as it reaches it, in one
//! pass: the generated code's first pass collects nothing (`collect`), and
//! the second pass it would make for leanrt's own scheduler, which ran a
//! task when it was waited for, never happens (`rewalk`, `before`).
//!
//! A walk is a handle (`begin`) to its state. Walks can nest (waiting for a
//! task can evaluate another constant) and interleave (a context of the
//! scheduler can block in one), so the state is not global.

use std::any::Any;
use std::collections::HashSet;
use std::hash::{BuildHasherDefault, Hasher};
use std::mem::size_of;

/// Hashes a cell address (a multiple of 8).
#[derive(Default)]
struct AddrHasher(u64);

impl Hasher for AddrHasher {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, _: &[u8]) {
        unreachable!()
    }
    fn write_usize(&mut self, n: usize) {
        self.0 = (n as u64 >> 3).wrapping_mul(0x9e3779b97f4a7c15);
    }
}

struct Walk {
    seen: HashSet<usize, BuildHasherDefault<AddrHasher>>,
    /// A reference to each value the walk read out of a thunk, a task or an
    /// `IO.Ref`, released when the walk ends. The cells the walk has seen
    /// stay alive meanwhile: they are reached from the constant (held by its
    /// caller) through fields, array elements and captured values, which do
    /// not change, and through the states of thunks and tasks and the values
    /// of references, which do (a thunk forced by a task the walk ran drops
    /// its computation): a cell freed meanwhile could give its address to a
    /// new cell, which the walk would then skip.
    kept: Vec<Box<dyn Any>>,
}

/// A new walk.
pub fn begin() -> u64 {
    let w = Box::new(Walk { seen: HashSet::default(), kept: Vec::new() });
    Box::into_raw(w) as u64
}

/// Whether walk `h` has already seen cell `v` (a shared value: a record,
/// an array, a thunk or task, a function value, a reference); otherwise it
/// records it.
#[inline(never)]
pub fn seen<T>(h: u64, v: T) -> bool {
    if size_of::<T>() != size_of::<usize>() {
        return false;
    }
    let p = unsafe { *(&v as *const T as *const usize) };
    let w = unsafe { &mut *(h as *mut Walk) };
    !w.seen.insert(p)
}

/// Walk `h` keeps `v` (a value read out of a thunk, a task or a reference)
/// until it ends. Returns 0.
#[inline(never)]
pub fn keep<T: 'static>(h: u64, v: T) -> u64 {
    let w = unsafe { &mut *(h as *mut Walk) };
    w.kept.push(Box::new(v));
    0
}

/// In the generated walk's first pass, whether the unfinished task with
/// address `a` is collected rather than waited for: never (see the module
/// comment); the walk waits for it, then looks into its value.
#[inline(never)]
pub fn collect(_h: u64, _a: usize) -> bool {
    false
}

/// The end of the generated walk's first pass: whether a second is needed.
/// Never: nothing was collected.
#[inline(never)]
pub fn rewalk(_h: u64) -> bool {
    false
}

/// Before the generated walk waits for task `a`: a collected task to run
/// first. None (`u64::MAX`): lean-runtime's `wait` runs the queue in the
/// workers' order.
#[inline(never)]
pub fn before(_h: u64, _a: usize) -> u64 {
    u64::MAX
}

/// The end of walk `h`. Returns 0.
#[inline(never)]
pub fn end(h: u64) -> u64 {
    drop(unsafe { Box::from_raw(h as *mut Walk) });
    0
}
