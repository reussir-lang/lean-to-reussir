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
//! out), whatever order the walk waits for them in. Here a pending task
//! runs when it is waited for, so the walk has two passes. The first only
//! collects the unfinished tasks it reaches (`collect`; it does not look
//! into them, their values do not exist yet). The second walks the value
//! again (`rewalk`) and, before it waits for a task, runs the collected
//! tasks that come before it in the workers' order (`before`), so that they
//! run in that order, as on the lone worker of `LEAN_NUM_THREADS=1`.
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
    /// The first pass, which collects unfinished tasks.
    collecting: bool,
    /// The unfinished tasks the first pass reached: their place in the
    /// workers' order (`task::persist_key`), a reference to each, and its
    /// address; after the first pass sorted with the first to run last.
    pending: Vec<(u64, Box<dyn Any>, usize)>,
    /// `task::serial_base` when the walk began.
    base: u32,
}

/// A new walk.
pub fn begin() -> u64 {
    let w = Box::new(Walk {
        seen: HashSet::default(),
        kept: Vec::new(),
        collecting: true,
        pending: Vec::new(),
        base: crate::task::serial_base(),
    });
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

/// In walk `h`'s first pass, whether task `v` (a task cell) is unfinished:
/// then it is collected, and the walk does not look into it. Always false
/// in the second pass.
#[inline(never)]
pub fn collect<T: 'static>(h: u64, v: T) -> bool {
    let w = unsafe { &mut *(h as *mut Walk) };
    if !w.collecting || size_of::<T>() != size_of::<usize>() {
        return false;
    }
    let p = unsafe { *(&v as *const T as *const usize) };
    match crate::task::persist_key(p, w.base) {
        Some(k) => {
            w.pending.push((k, Box::new(v), p));
            true
        }
        None => false,
    }
}

/// The end of walk `h`'s first pass: whether a second is needed (a task was
/// collected). The second pass sees every cell again.
#[inline(never)]
pub fn rewalk(h: u64) -> bool {
    let w = unsafe { &mut *(h as *mut Walk) };
    w.collecting = false;
    w.seen.clear();
    w.pending.sort_by(|a, b| b.0.cmp(&a.0));
    !w.pending.is_empty()
}

/// In walk `h`'s second pass, before it waits for task `cell`: the next
/// collected task that comes before it in the workers' order and is still
/// queued, handed over to be run (its tag, `task::persist_hand`), or
/// `u64::MAX` when there is none (left).
#[inline(never)]
pub fn before(h: u64, cell: usize) -> u64 {
    let w = unsafe { &mut *(h as *mut Walk) };
    if w.collecting {
        return u64::MAX;
    }
    let Some(kt) = crate::task::persist_key(cell, w.base) else { return u64::MAX };
    while let Some(&(k, _, c)) = w.pending.last() {
        if k >= kt {
            break;
        }
        let (tag, itself) = crate::task::persist_hand(c);
        if tag != u64::MAX && !itself {
            // A dropped task handed to be deleted first: `c` again next.
            return tag;
        }
        w.pending.pop();
        if tag != u64::MAX {
            return tag;
        }
    }
    u64::MAX
}

/// The end of walk `h`. Returns 0.
#[inline(never)]
pub fn end(h: u64) -> u64 {
    drop(unsafe { Box::from_raw(h as *mut Walk) });
    0
}
