//! Pending releases shared with Reussir's scoped worklist.
//!
//! Foreign containers join the active destruction scope. Their incremental
//! steps yield to newly deferred children, preserving LIFO release order
//! without growing the native stack. Promise resolutions and stream hand-offs
//! run after the outermost scope exits, when they may execute Lean code.

use reussir_rt::drop_stack as ds;
use std::cell::Cell;

pub type Release = ds::Release;
pub type Step = ds::Step;
pub use ds::StepStatus;

thread_local! {
    static END_REQUESTED: Cell<bool> = const { Cell::new(false) };
}

#[inline(always)]
pub fn releasing() -> bool {
    ds::releasing()
}

/// Number of pending entries, including the current step.
#[inline(always)]
pub fn depth() -> usize {
    ds::depth()
}

/// Defer a step, completing it before returning when no scope is active.
#[inline(always)]
pub fn defer_step(p: usize, step: Step) {
    unsafe { ds::defer_step(p as *mut std::ffi::c_void, step) }
}

/// Join an existing scope or complete the step in a new scope.
#[inline(always)]
pub fn run_step(p: usize, step: Step) {
    unsafe { ds::join_or_run_step(p as *mut std::ffi::c_void, step) }
}

/// Defer a cell without modifying its storage.
///
/// # Safety
/// The non-null cell must remain valid for `release` until it runs.
#[inline(always)]
pub unsafe fn defer_cell(cell: *mut u8, release: Release) {
    unsafe { ds::defer(cell, release) }
}

/// Request end work once for the active outermost scope.
#[inline(always)]
pub fn want_end_work() {
    debug_assert!(releasing(), "leanrt: end work asked for outside a drain");
    if !END_REQUESTED.replace(true) {
        ds::defer_until_scope_exit(end_work);
    }
}

fn end_work() {
    END_REQUESTED.set(false);
    #[cfg(test)]
    tests::END_SEEN.with(|s| s.borrow_mut().push((releasing(), depth())));
    crate::task::drained();
}

#[cfg(test)]
#[path = "pending_tests.rs"]
mod tests;
