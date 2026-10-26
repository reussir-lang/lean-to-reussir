//! leanrt's stack of pending releases: the thread's stack of pending drops
//! that it shares with Reussir's drop glue (reussir-rt's `drop_stack`).
//!
//! Freeing a value releases the objects it holds, and theirs, and so on.
//! Doing that by recursion takes stack proportional to the depth of the
//! value, so the frees push the objects they release on one stack of
//! pending work per thread instead, as Lean's `lean_del` does with its
//! to-do list, and the outermost free empties it ([`drain`]), last pushed
//! first. The depth of the native stack stays bounded however deep the
//! value is (a chain of boxes, of arrays, of thunks, of records), and the
//! releases that can be observed (a stream's close, a promise's drop) come
//! in native Lean's order.
//!
//! The stack is Reussir's: its drop glue defers the dead children of the
//! records it frees there (Reussir issue 23), and leanrt defers its own
//! work there: so one drain pops both in one order. A hook that finds
//! [`releasing`] true (a drain runs, Reussir's or leanrt's) pushes its work
//! and returns; one that finds it false is the outermost free: it pushes
//! its work and drains, which sets the flag, pops until nothing is left,
//! clears the flag and then runs the end work, if a release asked for it
//! ([`want_end_work`]: promise resolutions and stream hand-offs, which may
//! run Lean code or switch contexts, so not inside a drain). So the stack
//! is empty whenever the flag is clear.
//!
//! Two kinds of entries:
//! - a step ([`defer_step`], [`run_step`]): incremental work that stays on
//!   the stack while it runs, so whatever it pushes is done before its next
//!   step (an array's free, `drop::step_vec`; [`depth`] tells a step
//!   whether a release it made pushed work);
//! - a cell ([`defer_cell`]): a record or a box's program payload, to be
//!   released with a given function. Cells pushed one after the other with
//!   one release function form one run, one pointer (8 bytes) per cell (the
//!   boxed heads of a list that Reussir's glue frees whole). The stack never
//!   reads or writes a pending cell, so it does not depend on the cell's
//!   layout.
//!
//! The code was lean2rr's own (local Reussir patches 13-b, 13-c, 40-a, then
//! leanrt's pending stack beside Reussir's in the Phase 2 port); entry 23's
//! patches 23-k to 23-m gave Reussir's drop stack its runs, steps, depth and
//! end work, and leanrt now uses it. The state is the thread's, shared by
//! all of the thread's contexts: no context may switch inside a drain
//! (`sched::LeanrtGlue::switched` checks it in debug builds), and no Lean
//! code runs inside one (the end work runs after it).

use reussir_rt::drop_stack as ds;

/// Releases one pending cell, given the pointer it was deferred with.
pub type Release = ds::Release;

/// One step of incremental work on `p`; answers whether the work is done.
pub type Step = ds::Step;

/// Whether the current thread is emptying its pending stack (a drain of
/// Reussir's glue or of leanrt's frees): a release started now is pushed and
/// done by that drain.
#[inline(always)]
pub fn releasing() -> bool {
    ds::releasing()
}

/// The number of entries on the pending stack. Work pushed while a step runs
/// (the step is then the top entry) makes a new entry, so a step can tell
/// whether a release it made pushed work. 0 whenever [`releasing`] is false.
#[inline(always)]
pub fn depth() -> usize {
    ds::depth()
}

/// Pushes incremental work: `step(p)` runs, while the entry stays on the
/// stack, until it answers that it is done. Outside a drain, call [`drain`]
/// right after ([`run_step`]).
#[inline(always)]
pub fn defer_step(p: usize, step: Step) {
    unsafe { ds::defer_step(p, step) }
}

/// Runs incremental work and everything it pushes; inside a drain, only
/// pushes it.
#[inline(always)]
pub fn run_step(p: usize, step: Step) {
    unsafe { ds::run_step(p, step) }
}

/// Defers `release(cell)` until the current thread's drain pops it; outside a
/// drain, releases it at once, as the drain of that one cell, and then what
/// it pushed. `cell` is only kept and passed to `release`: the stack neither
/// reads nor writes it.
///
/// # Safety
/// `release(cell)` must be sound when it runs.
#[inline(always)]
pub unsafe fn defer_cell(cell: *mut u8, release: Release) {
    unsafe { ds::defer(cell, release) }
}

/// Runs the current thread's pending work, last pushed first, until none is
/// left, including the work it pushes in turn; then, if a release asked for
/// it ([`want_end_work`]), the end work (`task::drained`), with the flag
/// clear and nothing pending. A call made while the thread is already
/// draining (from a release) returns at once: the outermost call runs
/// whatever is pushed meanwhile.
#[inline(always)]
pub fn drain() {
    ds::drain()
}

/// Asks the running drain to run the end work once it is over
/// (`task::drained`: the promise resolutions put off inside the drain, then
/// lean-runtime's `after_drain`). Only inside a drain ([`releasing`]); the
/// request is used up by the drain's end. The end function is registered
/// with the stack at each request (one store).
#[inline(always)]
pub fn want_end_work() {
    debug_assert!(releasing(), "leanrt: end work asked for outside a drain");
    ds::set_end_work(end_work);
    ds::want_end_work();
}

/// The end work, called by the stack once its outermost drain is over.
unsafe extern "C" fn end_work() {
    #[cfg(test)]
    tests::END_SEEN.with(|s| s.borrow_mut().push((releasing(), depth())));
    crate::task::drained();
}

#[cfg(test)]
#[path = "pending_tests.rs"]
mod tests;
