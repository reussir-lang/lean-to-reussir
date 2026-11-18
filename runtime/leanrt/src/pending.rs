//! leanrt's pending releases: a thin layer over the thread's worklist of
//! pending drops that leanrt shares with Reussir's drop glue (reussir-rt's
//! `drop_stack`, upstream's scoped worklists).
//!
//! Freeing a value releases the objects it holds, and theirs, and so on.
//! Doing that by recursion takes stack proportional to the depth of the
//! value, so the frees put the objects they release on one worklist per
//! thread instead, as Lean's `lean_del` does with its to-do list, and the
//! outermost free empties it, last pushed first. The depth of the native
//! stack stays bounded however deep the value is (a chain of boxes, of
//! arrays, of thunks, of records), and the releases that can be observed
//! (a stream's close, a promise's drop) come in native Lean's order.
//!
//! The worklist is Reussir's: its drop glue defers the dead children of
//! the records it frees there, and leanrt defers its own work there, so
//! both are popped in one order. The work belongs to a *scope*. The
//! outermost free opens one: a function of this module that finds
//! [`releasing`] false ([`defer_cell`], [`defer_step`], [`run_step`]) puts
//! its work in a new scope and returns only when the scope is over, that
//! is when the work and everything it pushed is done. One that finds
//! [`releasing`] true joins the running scope: it pushes its work and
//! returns, and the scope does the work later. So nothing is pending
//! whenever [`releasing`] is false, and there is no `drain` to call: a
//! scope ends by itself. (Reussir's own entry points for a free that must
//! be complete at its return, `drop_stack::run`, open a nested scope inside
//! a running one, which finishes its own work and leaves the older work
//! pending. leanrt calls none of them.)
//!
//! Two kinds of entries:
//! - a step ([`defer_step`], [`run_step`]): incremental work that stays on
//!   the worklist while it runs. The scope calls the step again and again
//!   until it answers [`StepStatus::Complete`]; whatever a call pushed is
//!   done before the next call (an array's free, `drop::step_vec`:
//!   [`depth`] tells a step whether a release it made pushed work, and it
//!   then answers [`StepStatus::Pending`]);
//! - a cell ([`defer_cell`]): a record or a box's program payload, to be
//!   released with a given function. Cells pushed one after the other with
//!   one release function form one run, one pointer (8 bytes) per cell (the
//!   boxed heads of a list that Reussir's glue frees whole). The worklist
//!   never reads or writes a pending cell, so it does not depend on the
//!   cell's layout.
//!
//! The argument of a step and the pointer of a cell must not be null: the
//! worklist keeps them as non-null pointers without a check
//! (`NonNull::new_unchecked`), so a null one is undefined behaviour, and
//! in practice the worklist would read it as "no run of cells" and never
//! release the cells of the run. leanrt passes addresses of live objects;
//! debug builds check it here.
//!
//! The end work ([`want_end_work`]: promise resolutions and stream
//! hand-offs) may run Lean code or switch contexts, so it must not run
//! inside a scope. It is a scope-exit callback: the worklist calls it after
//! the outermost scope is over, with [`releasing`] false and nothing
//! pending. The worklist takes a plain Rust function for it; its body is an
//! `extern "C"` function, so a panic in the end work aborts the process
//! there, as in a release or a step, and does not unwind into the function
//! that started the free.
//!
//! History: the code was lean2rr's own (local Reussir patches 13-b, 13-c,
//! 40-a, then leanrt's pending stack beside Reussir's, then local patches
//! 23-k to 23-m on Reussir's drop stack). Upstream Reussir now has the
//! worklist with runs, steps, depth and scope-exit callbacks, and this
//! module only names them for leanrt. The state is the thread's, shared by
//! all of the thread's contexts: no context may switch inside a scope
//! (`sched::LeanrtGlue::switched` checks it in debug builds), and no Lean
//! code runs inside one (the end work runs after it).

use reussir_rt::drop_stack as ds;
use std::cell::Cell;

/// Releases one pending cell, given the pointer it was deferred with.
pub type Release = ds::Release;

/// One step of incremental work on its argument (the pointer the step was
/// deferred with); answers whether the work is done ([`StepStatus`]).
pub type Step = ds::Step;

/// A step's answer: `Complete` (the work is done; the entry is removed) or
/// `Pending` (call again, after the work that this call pushed).
pub use ds::StepStatus;

thread_local! {
    /// Whether the end work is already requested for the thread's running
    /// outermost scope ([`want_end_work`]). Set by the first request,
    /// cleared by the end work itself, at its start. No destructor (a
    /// `const` cell of a `bool`), so a free in a thread-local destructor
    /// can still read it.
    static END_REQUESTED: Cell<bool> = const { Cell::new(false) };
}

/// Whether the current thread has a scope running (a free of Reussir's glue
/// or of leanrt): a release started now is pushed and done by that scope.
#[inline(always)]
pub fn releasing() -> bool {
    ds::releasing()
}

/// The number of entries on the worklist: the suspended ones, and one for
/// the run of cells being released, if there is one. A step that runs is
/// an entry; work pushed while it runs makes a new entry, so a step can
/// tell whether a release it made pushed work. 0 whenever [`releasing`] is
/// false.
#[inline(always)]
pub fn depth() -> usize {
    ds::depth()
}

/// Pushes incremental work: `step(p)` is called, while the entry stays on
/// the worklist, until it answers [`StepStatus::Complete`]. Inside a scope
/// it only pushes; outside one it opens a scope, so the step and everything
/// it pushes is done at the return. `p` must not be 0 (module
/// documentation), and must stay valid for `step` until the step is
/// complete.
#[inline(always)]
pub fn defer_step(p: usize, step: Step) {
    debug_assert!(p != 0, "leanrt: a step deferred with a null argument");
    unsafe { ds::defer_step(p as *mut std::ffi::c_void, step) }
}

/// Runs incremental work and everything it pushes; inside a scope, only
/// pushes it (it joins the scope: `drop_stack::join_or_run_step`). The same
/// behaviour as [`defer_step`]; the name says that the caller is where a
/// free can start. `p` as for [`defer_step`].
#[inline(always)]
pub fn run_step(p: usize, step: Step) {
    debug_assert!(p != 0, "leanrt: a step run with a null argument");
    unsafe { ds::join_or_run_step(p as *mut std::ffi::c_void, step) }
}

/// Defers `release(cell)` until the running scope pops it; outside a scope,
/// releases it at once in a scope of its own, and then what it pushed.
/// `cell` is only kept and passed to `release`: the worklist neither reads
/// nor writes it.
///
/// # Safety
/// `cell` is not null, and `release(cell)` must be sound when it runs.
#[inline(always)]
pub unsafe fn defer_cell(cell: *mut u8, release: Release) {
    debug_assert!(!cell.is_null(), "leanrt: a null cell deferred");
    unsafe { ds::defer(cell, release) }
}

/// Asks for the end work once the running outermost scope is over
/// (`task::drained`: the promise resolutions put off inside the scope, then
/// lean-runtime's `after_drain`). Only inside a scope ([`releasing`]).
///
/// The worklist keeps one callback per request
/// (`drop_stack::defer_until_scope_exit` is a queue and does not look for
/// duplicates), and a free can ask once per stream or promise it releases.
/// So only the first request of a scope registers the callback
/// (`END_REQUESTED`), and the end work runs once per outermost scope. The
/// end work clears the flag before it does anything: it can start a new
/// free, whose requests are for that free's scope.
///
/// A scope ends without its exit callbacks only when a panic unwinds
/// through it; the flag then stays set, and the callback stays queued for
/// the thread's next outermost scope (in a thread-local destructor, where
/// the scope has a context of its own, it is lost). Releases, steps and the
/// end work are `extern "C"` functions, where a panic aborts the process.
#[inline(always)]
pub fn want_end_work() {
    debug_assert!(releasing(), "leanrt: end work asked for outside a drain");
    if !END_REQUESTED.replace(true) {
        ds::defer_until_scope_exit(end_work);
    }
}

/// The end work, called by the worklist after its outermost scope is over.
fn end_work() {
    /// The body: `extern "C"`, so that a panic aborts here.
    extern "C" fn run() {
        END_REQUESTED.set(false);
        #[cfg(test)]
        tests::END_SEEN.with(|s| s.borrow_mut().push((releasing(), depth())));
        crate::task::drained();
    }
    run()
}

#[cfg(test)]
#[path = "pending_tests.rs"]
mod tests;
