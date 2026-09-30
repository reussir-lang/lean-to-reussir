//! Bookkeeping for deferred tasks.
//!
//! The runtime is single-threaded. A task is a runtime cell (`LCell`) whose
//! state lean2rr generates: `pending(action)`, `busy` or `done(value)`. IO
//! tasks (`IO.asTask`, `IO.mapTask`, `IO.bindTask`) stay pending until the
//! program first needs them, and otherwise run when `main` returns, like
//! Lean's task manager, which finishes every queued task before the process
//! exits. Pure tasks are computed when they are created, except while some
//! task is pending or running: then they are deferred too, since their code
//! might need such a task (which may be waiting for `main`). Each of these
//! schedules is one a native thread pool can produce (a worker may start a
//! task at any time after it is created). See translation plan §5.14.
//!
//! This module holds what the generated code cannot: the queue of pending
//! tasks (in creation order; it owns one reference to each cell), the stack
//! of running tasks, cancellation flags and their propagation to dependent
//! tasks, and the phase of the program. A task is identified by the address
//! of its cell, which is stable while the queue or a running computation
//! holds it: every pending task cell is queued, and entries about a task are
//! dropped when it finishes. (A task converted to another representation is
//! a new cell that records the address of the task it stands for, and keeps
//! that task alive; questions about it are asked about that address.)

use std::cell::UnsafeCell;
use std::collections::{BTreeMap, BTreeSet};

struct Global<T>(UnsafeCell<T>);
unsafe impl<T> Sync for Global<T> {}

struct Entry {
    /// Position in the queue (creation order, or the order in which the
    /// task it waits for finished; negative: at the head).
    seq: i64,
    /// Which generated state type the cell has (lean2rr's tag).
    tag: u64,
    /// `IO.getTaskState` reported this task as waiting: the sleep count at
    /// the first such answer, and the number of answers.
    observed: Option<u64>,
    queries: u32,
    /// Created depending on a task that was unfinished then (`mapTask`,
    /// `bindTask`): off the queue until that task finishes.
    waiting: bool,
    /// Created with `sync := true`: when the task it waits for finishes,
    /// Lean runs it at once (`LEAN_SYNC_PRIO` in `enqueue_core`).
    sync: bool,
}

struct Running {
    cell: usize,
    /// `IO.checkCanceled` was called in this run.
    checked: bool,
    /// The sleep count when the run started.
    epoch: u64,
}

struct Tasks {
    /// `main` is running. Before (during module initialization) Lean has no
    /// task manager and runs every task at once.
    started: bool,
    /// `main` has returned; the remaining tasks run as during Lean's
    /// task-manager shutdown.
    shutting_down: bool,
    next_seq: i64,
    /// For tasks that go to the head of the queue (decreasing).
    head_seq: i64,
    /// Sleeps so far (`IO.sleep`, `dbgSleep`): time passing, for the
    /// heuristics below.
    epoch: u64,
    /// Pending tasks that do not wait for another task, in the order Lean's
    /// task manager enqueues them: seq -> cell address. A task that waits
    /// for another is enqueued when that one finishes, and several such
    /// tasks newest first, as Lean's `handle_finished` walks its dependents.
    queue: BTreeMap<i64, usize>,
    /// Pending tasks by cell address.
    pending: BTreeMap<usize, Entry>,
    /// Unfinished tasks for which `IO.cancel` was called.
    canceled: BTreeSet<usize>,
    /// Unfinished task -> the tasks created while it was unfinished that
    /// depend on it (`mapTask`, `bindTask`): they are canceled when it
    /// finishes canceled, as Lean's `handle_finished` does.
    deps: BTreeMap<usize, Vec<usize>>,
    /// Running tasks, innermost last.
    running: Vec<Running>,
}

static TASKS: Global<Tasks> = Global(UnsafeCell::new(Tasks {
    started: false,
    shutting_down: false,
    next_seq: 0,
    head_seq: -1,
    epoch: 0,
    queue: BTreeMap::new(),
    pending: BTreeMap::new(),
    canceled: BTreeSet::new(),
    deps: BTreeMap::new(),
    running: Vec::new(),
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

/// Whether a new pure task is computed at once: during initialization, or
/// when no task is pending or running (so its code cannot need one).
#[inline]
pub fn eager_pure() -> bool {
    let t = tasks();
    !t.started || (t.pending.is_empty() && t.running.is_empty())
}

/// `main` has returned; the remaining tasks are about to run.
pub fn shutdown() {
    tasks().shutting_down = true;
}

/// `IO.sleep` / `dbgSleep`.
#[inline(never)]
pub fn sleep_ms(ms: u32) {
    tasks().epoch += 1;
    std::thread::sleep(std::time::Duration::from_millis(ms as u64));
}

/// Queue a pending task. The queue takes over one reference to the cell at
/// `cell`.
#[inline(never)]
pub fn register(cell: usize, tag: u64) {
    let t = tasks();
    let seq = t.next_seq;
    t.next_seq += 1;
    t.queue.insert(seq, cell);
    t.pending.insert(cell, Entry { seq, tag, observed: None, queries: 0, waiting: false, sync: false });
}

/// `dep` was created depending on `src` (`sync`: with `sync := true`): if
/// `src` is unfinished, `dep` waits for it (in the final run of queued
/// tasks), and will be canceled if `src` finishes canceled, as Lean's
/// `add_dep` and `handle_finished` do.
#[inline(never)]
pub fn depend(src: usize, dep: usize, sync: bool) {
    if status(src) != 2 {
        let t = tasks();
        t.deps.entry(src).or_default().push(dep);
        if let Some(e) = t.pending.get_mut(&dep) {
            e.sync = sync;
            if !e.waiting {
                e.waiting = true;
                t.queue.remove(&e.seq);
            }
        }
    }
}

fn is_running(cell: usize) -> bool {
    tasks().running.iter().any(|r| r.cell == cell)
}

/// A task starts running. Returns whether the queue held a reference to the
/// cell, which the caller must now release.
#[inline(never)]
pub fn begin(cell: usize) -> bool {
    let t = tasks();
    t.running.push(Running { cell, checked: false, epoch: t.epoch });
    match t.pending.remove(&cell) {
        Some(e) => {
            if !e.waiting {
                t.queue.remove(&e.seq);
            }
            true
        }
        None => false,
    }
}

/// The running task `cell` stops without finishing: it will run again (a
/// `bind` task waiting for the task it continues as). Its flag and its
/// dependents stay.
#[inline(never)]
pub fn suspend(cell: usize) {
    let top = tasks().running.pop();
    debug_assert_eq!(top.map(|r| r.cell), Some(cell));
}

/// The running task `cell` has finished: the tasks that depend on it are
/// ready (Lean enqueues them newest first), and canceled too if it was.
#[inline(never)]
pub fn end(cell: usize) {
    let t = tasks();
    let top = t.running.pop();
    debug_assert_eq!(top.map(|r| r.cell), Some(cell));
    let canceled = t.canceled.remove(&cell);
    if let Some(ds) = t.deps.remove(&cell) {
        // Lean walks the dependents from the newest: `sync` ones run at once
        // (so, here, at the head of the queue, in walk order), the others are
        // enqueued.
        let mut syncs = Vec::new();
        for &d in ds.iter().rev() {
            let running = is_running(d);
            let t = tasks();
            if let Some(e) = t.pending.get_mut(&d) {
                if e.waiting {
                    e.waiting = false;
                    if e.sync {
                        syncs.push(d);
                    } else {
                        e.seq = t.next_seq;
                        t.next_seq += 1;
                        t.queue.insert(e.seq, d);
                    }
                }
            }
            if canceled && (running || t.pending.contains_key(&d)) {
                t.canceled.insert(d);
            }
        }
        let t = tasks();
        for &d in syncs.iter().rev() {
            if let Some(e) = t.pending.get_mut(&d) {
                e.seq = t.head_seq;
                t.head_seq -= 1;
                t.queue.insert(e.seq, d);
            }
        }
    }
}

/// The state of a task: 0 waiting (pending), 1 running, 2 finished.
#[inline(never)]
pub fn status(cell: usize) -> u8 {
    if is_running(cell) {
        return 1;
    }
    if tasks().pending.contains_key(&cell) { 0 } else { 2 }
}

/// `IO.getTaskState`: 0 waiting, 1 running, 2 finished, or 3: the caller
/// runs the task and reports it finished. A pending task is reported
/// waiting until the program asks again after some time has passed (a
/// sleep) or keeps asking (a busy loop): it is then polling for the task,
/// which a worker would have run meanwhile.
#[inline(never)]
pub fn query(cell: usize) -> u8 {
    let s = status(cell);
    if s != 0 {
        return s;
    }
    let t = tasks();
    let epoch = t.epoch;
    let Some(e) = t.pending.get_mut(&cell) else { return 3 };
    match e.observed {
        None => {
            e.observed = Some(epoch);
            e.queries = 1;
            0
        }
        Some(first) if epoch > first || e.queries >= 1000 => 3,
        Some(_) => {
            e.queries += 1;
            0
        }
    }
}

/// `IO.cancel` of a task.
#[inline(never)]
pub fn cancel(cell: usize) {
    if tasks().pending.contains_key(&cell) || is_running(cell) {
        tasks().canceled.insert(cell);
    }
}

/// `IO.checkCanceled`: inside a task, whether it was canceled or the program
/// is shutting down; always false in `main`. At shutdown, Lean sets its flag
/// while the remaining tasks run: a task sees it once time has passed in it
/// (a sleep) or from its second check on.
#[inline(never)]
pub fn check_canceled() -> bool {
    let t = tasks();
    let epoch = t.epoch;
    let shutting_down = t.shutting_down;
    let Some(top) = t.running.last_mut() else { return false };
    let cell = top.cell;
    let late = if shutting_down {
        let seen = top.checked || epoch > top.epoch;
        top.checked = true;
        seen
    } else {
        false
    };
    late || t.canceled.contains(&cell)
}

/// The next task of the final run of queued tasks: the first of the queue
/// (see `Tasks::queue`). When only tasks waiting for others remain (a
/// cycle), there is none: Lean's workers stop when the queue is empty and
/// leave such tasks behind.
fn next() -> Option<usize> {
    tasks().queue.values().next().copied()
}

/// The tag of the next task (see `next`), `u64::MAX` if there is none.
#[inline(never)]
pub fn next_tag() -> u64 {
    match next() {
        Some(cell) => tasks().pending[&cell].tag,
        None => u64::MAX,
    }
}

/// Remove the next task (see `next`) from the queue and hand its reference
/// to the caller.
#[inline(never)]
pub fn take() -> usize {
    let cell = next().expect("leanrt: no pending task");
    let t = tasks();
    let e = t.pending.remove(&cell).expect("leanrt: no pending task");
    if !e.waiting {
        t.queue.remove(&e.seq);
    }
    cell
}

/// A thunk forced from its own computation, or tasks waiting for each other:
/// native Lean waits forever (without flushing stdout).
pub fn hang() -> ! {
    loop {
        std::thread::sleep(std::time::Duration::from_secs(3600));
    }
}
