//! Bookkeeping for deferred IO tasks (`IO.asTask`, `IO.mapTask`,
//! `IO.bindTask`).
//!
//! The runtime is single-threaded. A task is a runtime cell (`LCell`) whose
//! state lean2rr generates: `pending(action)`, `busy` or `done(value)`. An
//! IO task stays pending until the program first needs it (`IO.wait`,
//! `Task.get`, `IO.waitAny`, a second `IO.getTaskState`) and otherwise runs
//! when `main` returns, like Lean's task manager, which finishes every queued
//! task before the process exits. Each of these schedules is one a native
//! thread pool can produce (a worker may start a task at any time after it is
//! created).
//!
//! This module holds what the generated code cannot: the queue of pending IO
//! tasks (in creation order; it owns one reference to each cell), the stack
//! of running tasks (for `IO.checkCanceled`), the cancellation flags and the
//! phase of the program. Cells are identified by their address, which is
//! stable while the queue or a running computation holds them.

use std::cell::UnsafeCell;
use std::collections::{BTreeMap, BTreeSet};

struct Global<T>(UnsafeCell<T>);
unsafe impl<T> Sync for Global<T> {}

struct Entry {
    /// Position in the creation-order queue.
    seq: u64,
    /// Which generated state type the cell has (lean2rr's tag).
    tag: u64,
    /// `IO.getTaskState` has already reported this task as waiting.
    observed: bool,
}

struct Tasks {
    /// `main` is running: IO tasks are deferred. Before (during module
    /// initialization) Lean has no task manager and runs them at once.
    started: bool,
    /// `main` has returned: remaining tasks run with `IO.checkCanceled`
    /// true, as during Lean's task-manager shutdown.
    shutting_down: bool,
    next_seq: u64,
    /// Pending IO tasks: seq -> cell address.
    queue: BTreeMap<u64, usize>,
    /// Pending IO tasks by cell address.
    pending: BTreeMap<usize, Entry>,
    /// Pending or running tasks for which `IO.cancel` was called.
    canceled: BTreeSet<usize>,
    /// Running tasks, innermost last.
    current: Vec<usize>,
}

static TASKS: Global<Tasks> = Global(UnsafeCell::new(Tasks {
    started: false,
    shutting_down: false,
    next_seq: 0,
    queue: BTreeMap::new(),
    pending: BTreeMap::new(),
    canceled: BTreeSet::new(),
    current: Vec::new(),
}));

#[inline]
fn tasks() -> &'static mut Tasks {
    unsafe { &mut *TASKS.0.get() }
}

/// The entry point calls this right before `main`
/// (`lean_io_mark_end_initialization` + `lean_init_task_manager`).
pub fn start() {
    tasks().started = true;
}

/// Whether new IO tasks are deferred (otherwise they run at once).
#[inline]
pub fn deferring() -> bool {
    tasks().started
}

/// `main` has returned; the remaining tasks are about to run.
pub fn shutdown() {
    tasks().shutting_down = true;
}

/// Queue a pending IO task. The queue takes over one reference to the cell
/// at `cell`.
#[inline(never)]
pub fn register(cell: usize, tag: u64) {
    let t = tasks();
    let seq = t.next_seq;
    t.next_seq += 1;
    t.queue.insert(seq, cell);
    t.pending.insert(cell, Entry { seq, tag, observed: false });
}

/// A task starts running. Returns whether the queue held a reference to the
/// cell, which the caller must now release.
#[inline(never)]
pub fn begin(cell: usize) -> bool {
    let t = tasks();
    t.current.push(cell);
    match t.pending.remove(&cell) {
        Some(e) => {
            t.queue.remove(&e.seq);
            true
        }
        None => false,
    }
}

/// The running task `cell` has finished.
#[inline(never)]
pub fn end(cell: usize) {
    let t = tasks();
    let top = t.current.pop();
    debug_assert_eq!(top, Some(cell));
    t.canceled.remove(&cell);
}

/// `IO.cancel` of an unfinished task.
#[inline(never)]
pub fn cancel(cell: usize) {
    let t = tasks();
    if t.pending.contains_key(&cell) || t.current.contains(&cell) {
        t.canceled.insert(cell);
    }
}

/// `IO.checkCanceled`: inside a task, whether it was canceled or the program
/// is shutting down; always false in the main thread.
#[inline(never)]
pub fn check_canceled() -> bool {
    let t = tasks();
    match t.current.last() {
        Some(c) => t.shutting_down || t.canceled.contains(c),
        None => false,
    }
}

/// `IO.getTaskState` of a pending task: the first query of a task reports
/// it as waiting (returns false); a later one means the program is polling
/// for it, and the caller runs it first (returns true).
#[inline(never)]
pub fn observe(cell: usize) -> bool {
    match tasks().pending.get_mut(&cell) {
        Some(e) if !e.observed => {
            e.observed = true;
            false
        }
        _ => true,
    }
}

/// The tag of the oldest pending task, `u64::MAX` if there is none.
#[inline(never)]
pub fn next_tag() -> u64 {
    let t = tasks();
    match t.queue.first_key_value() {
        Some((_, cell)) => t.pending[cell].tag,
        None => u64::MAX,
    }
}

/// Remove the oldest pending task from the queue and hand its reference to
/// the caller.
#[inline(never)]
pub fn take() -> usize {
    let t = tasks();
    let (_, cell) = t.queue.pop_first().expect("leanrt: no pending task");
    t.pending.remove(&cell);
    cell
}

/// A thunk forced from its own computation, or tasks waiting for each other:
/// native Lean waits forever (without flushing stdout).
pub fn hang() -> ! {
    loop {
        std::thread::sleep(std::time::Duration::from_secs(3600));
    }
}
