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
//! tasks, the tasks that stand for another one (a task converted to another
//! representation), and the phase of the program. A cell is identified by
//! its address, which is stable while the queue or a running computation
//! holds it: every pending task cell is queued, and entries about a task are
//! dropped when it finishes.

use std::cell::UnsafeCell;
use std::collections::{BTreeMap, BTreeSet};

struct Global<T>(UnsafeCell<T>);
unsafe impl<T> Sync for Global<T> {}

struct Entry {
    /// Position in the creation-order queue.
    seq: u64,
    /// Which generated state type the cell has (lean2rr's tag).
    tag: u64,
    /// `IO.getTaskState` reported this task as waiting: the sleep count at
    /// the first such answer, and the number of answers.
    observed: Option<u64>,
    queries: u32,
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
    next_seq: u64,
    /// Sleeps so far (`IO.sleep`, `dbgSleep`): time passing, for the
    /// heuristics below.
    epoch: u64,
    /// Pending tasks: seq -> cell address.
    queue: BTreeMap<u64, usize>,
    /// Pending tasks by cell address.
    pending: BTreeMap<usize, Entry>,
    /// Unfinished tasks for which `IO.cancel` was called.
    canceled: BTreeSet<usize>,
    /// Unfinished task -> the tasks created while it was unfinished that
    /// depend on it (`mapTask`, `bindTask`): they are canceled when it
    /// finishes canceled, as Lean's `handle_finished` does.
    deps: BTreeMap<usize, Vec<usize>>,
    /// Unfinished converted task -> the task it stands for.
    aliases: BTreeMap<usize, usize>,
    /// Running tasks, innermost last.
    running: Vec<Running>,
}

static TASKS: Global<Tasks> = Global(UnsafeCell::new(Tasks {
    started: false,
    shutting_down: false,
    next_seq: 0,
    epoch: 0,
    queue: BTreeMap::new(),
    pending: BTreeMap::new(),
    canceled: BTreeSet::new(),
    deps: BTreeMap::new(),
    aliases: BTreeMap::new(),
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
    t.pending.insert(cell, Entry { seq, tag, observed: None, queries: 0 });
}

/// Queue a pending task that stands for the unfinished task `orig` (the
/// same Lean task at another representation): questions about it are
/// answered for `orig`, and it is canceled with `orig`.
#[inline(never)]
pub fn register_alias(cell: usize, tag: u64, orig: usize) {
    register(cell, tag);
    let t = tasks();
    t.aliases.insert(cell, orig);
    t.deps.entry(orig).or_default().push(cell);
}

/// `dep` was created depending on `src`: if `src` is unfinished, `dep`
/// will be canceled if `src` finishes canceled.
#[inline(never)]
pub fn depend(src: usize, dep: usize) {
    if status(src) != 2 {
        tasks().deps.entry(src).or_default().push(dep);
    }
}

/// The task a (possibly converted) task stands for.
fn origin(mut cell: usize) -> usize {
    let t = tasks();
    while let Some(&o) = t.aliases.get(&cell) {
        cell = o;
    }
    cell
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
            t.queue.remove(&e.seq);
            true
        }
        None => false,
    }
}

/// The running task `cell` has finished; if it was canceled, so are the
/// unfinished tasks that depend on it.
#[inline(never)]
pub fn end(cell: usize) {
    let t = tasks();
    let top = t.running.pop();
    debug_assert_eq!(top.map(|r| r.cell), Some(cell));
    t.aliases.remove(&cell);
    let canceled = t.canceled.remove(&cell);
    if let Some(ds) = t.deps.remove(&cell) {
        if canceled {
            for d in ds {
                if t.pending.contains_key(&d) || is_running(d) {
                    t.canceled.insert(d);
                }
            }
        }
    }
}

/// The state of a task: 0 waiting (pending), 1 running, 2 finished. A
/// converted task that has not run is in the state of the task it stands
/// for (finished then means its value is one conversion away).
#[inline(never)]
pub fn status(cell: usize) -> u8 {
    if is_running(cell) {
        return 1;
    }
    if !tasks().pending.contains_key(&cell) {
        return 2;
    }
    let o = origin(cell);
    if o == cell {
        0
    } else {
        status(o)
    }
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
    let o = origin(cell);
    let t = tasks();
    let epoch = t.epoch;
    let Some(e) = t.pending.get_mut(&o) else { return 3 };
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
    let o = origin(cell);
    let t = tasks();
    if t.pending.contains_key(&o) || is_running(o) {
        t.canceled.insert(o);
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
