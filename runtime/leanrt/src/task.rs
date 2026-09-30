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
//! This module holds what the generated code cannot: the queues of pending
//! tasks (one per priority, in the order Lean's task manager enqueues them;
//! they own one reference to each cell), the walk of a finished task's
//! dependents, the stack of running tasks, cancellation flags and their
//! propagation to dependent tasks, and the phase of the program. A task is identified by the address
//! of its cell, which is stable while the queue or a running computation
//! holds it: every pending task cell is queued, and entries about a task are
//! dropped when it finishes. (A task converted to another representation is
//! a new cell that records the address of the task it stands for, and keeps
//! that task alive; questions about it are asked about that address.)

use std::cell::UnsafeCell;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

struct Global<T>(UnsafeCell<T>);
unsafe impl<T> Sync for Global<T> {}

/// Priorities: Lean's 0..=8 (`Task.Priority.max`), and 9 for dedicated
/// tasks (a thread of their own natively, so started first here).
const PRIOS: usize = 10;

struct Entry {
    /// Position in its priority's queue (while not waiting).
    seq: i64,
    /// Which generated state type the cell has (lean2rr's tag).
    tag: u64,
    /// `IO.getTaskState` reported this task as waiting: the sleep count at
    /// the first such answer, and the number of answers.
    observed: Option<u64>,
    queries: u32,
    /// Waits for the task it depends on (`mapTask`, `bindTask`, `Task.map`,
    /// `Task.bind` of a task unfinished at its creation): off the queue until
    /// that task finishes.
    waiting: bool,
}

/// What stays known about an unfinished task (pending, running, or a bind
/// task waiting for its continuation), until it finishes.
struct Info {
    prio: usize,
    /// Created with `sync := true`: Lean runs it on the thread that finishes
    /// the task it waits for, as soon as that one finishes (`LEAN_SYNC_PRIO`
    /// in `enqueue_core`), also when it waits again (a bind task).
    sync: bool,
    /// The task it was created depending on, while that is unfinished.
    source: Option<usize>,
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
    /// Sleeps so far (`IO.sleep`, `dbgSleep`): time passing, for the
    /// heuristics below.
    epoch: u64,
    /// Pending tasks that do not wait for another task, one queue per
    /// priority as in Lean's task manager (the highest non-empty one is
    /// taken first), in the order they were enqueued: seq -> cell address.
    queues: [BTreeMap<i64, usize>; PRIOS],
    /// Pending tasks by cell address.
    pending: BTreeMap<usize, Entry>,
    /// Unfinished tasks.
    info: BTreeMap<usize, Info>,
    /// Unfinished tasks for which `IO.cancel` was called.
    canceled: BTreeSet<usize>,
    /// Unfinished task -> the tasks created while it was unfinished that
    /// depend on it, oldest first.
    deps: BTreeMap<usize, Vec<usize>>,
    /// The dependents of finished tasks still being walked (innermost
    /// last), newest dependent first, as Lean's `handle_finished` walks
    /// them: a `sync` one runs there and then, the others are enqueued.
    walks: Vec<(usize, VecDeque<usize>)>,
    /// A task handed to the generated code (`walk_next`, `source_next`)
    /// with the queue's reference, for `handed`.
    handed: Option<usize>,
    /// The task a native worker would be running: with one worker thread
    /// (`LEAN_NUM_THREADS=1`), an idle worker starts the first task queued
    /// and, when that finishes, the first of the highest non-empty queue at
    /// that moment. Such a started task runs first in the final run of
    /// queued tasks, whatever tasks are queued after it.
    worker: Option<usize>,
    /// For `source_next`: a task being forced and the pending tasks it waits
    /// for, still to run (deepest last), innermost last.
    chains: Vec<(usize, Vec<usize>)>,
    /// Running tasks, innermost last.
    running: Vec<Running>,
}

static TASKS: Global<Tasks> = Global(UnsafeCell::new(Tasks {
    started: false,
    shutting_down: false,
    next_seq: 0,
    epoch: 0,
    queues: [const { BTreeMap::new() }; PRIOS],
    pending: BTreeMap::new(),
    info: BTreeMap::new(),
    canceled: BTreeSet::new(),
    deps: BTreeMap::new(),
    walks: Vec::new(),
    handed: None,
    worker: None,
    chains: Vec::new(),
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

/// Queue a pending task at priority `prio` (Lean's `Task.Priority`; above
/// 8 is dedicated). The queue takes over one reference to the cell at
/// `cell`. A bind task queued again keeps its priority.
#[inline(never)]
pub fn register(cell: usize, tag: u64, prio: u64) {
    let t = tasks();
    let prio = t.info.entry(cell).or_insert(Info { prio: prio.min(PRIOS as u64 - 1) as usize, sync: false, source: None }).prio;
    let seq = t.next_seq;
    t.next_seq += 1;
    t.queues[prio].insert(seq, cell);
    t.pending.insert(cell, Entry { seq, tag, observed: None, queries: 0, waiting: false });
    if t.worker.is_none() && t.started && !t.shutting_down {
        t.worker = Some(cell);
    }
}

/// The worker is idle: it starts the next queued task (see `Tasks::worker`).
fn worker_idle() {
    let t = tasks();
    t.worker = next_queued();
}

/// `dep` was created depending on `src` (`sync`: with `sync := true`): if
/// `src` is unfinished, `dep` waits for it (in the final run of queued
/// tasks), runs or is enqueued when it finishes, and will be canceled if
/// `src` finishes canceled, as Lean's `add_dep` and `handle_finished` do.
#[inline(never)]
pub fn depend(src: usize, dep: usize, sync: bool) {
    if status(src) != 2 {
        let t = tasks();
        t.deps.entry(src).or_default().push(dep);
        if let Some(i) = t.info.get_mut(&dep) {
            i.sync |= sync;
            i.source = Some(src);
        }
        if let Some(e) = t.pending.get_mut(&dep) {
            if !e.waiting {
                e.waiting = true;
                let prio = t.info.get(&dep).map_or(0, |i| i.prio);
                t.queues[prio].remove(&e.seq);
            }
        }
        if t.worker == Some(dep) {
            worker_idle();
        }
    }
}

/// Remove a pending task from the queues (the caller takes the queue's
/// reference).
fn unqueue(cell: usize) -> bool {
    let t = tasks();
    match t.pending.remove(&cell) {
        Some(e) => {
            if !e.waiting {
                let prio = t.info.get(&cell).map_or(0, |i| i.prio);
                t.queues[prio].remove(&e.seq);
            }
            true
        }
        None => false,
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
    unqueue(cell)
}

/// The running task `cell` stops without finishing: it will run again (a
/// `bind` task waiting for the task it continues as). Its flags, priority
/// and dependents stay.
#[inline(never)]
pub fn suspend(cell: usize) {
    let top = tasks().running.pop();
    debug_assert_eq!(top.map(|r| r.cell), Some(cell));
    if tasks().worker == Some(cell) {
        worker_idle();
    }
}

/// The running task `cell` has finished: its dependents are to be walked
/// (`walk_next`, which the generated code calls next), and canceled too if
/// it was.
#[inline(never)]
pub fn end(cell: usize) {
    let t = tasks();
    let top = t.running.pop();
    debug_assert_eq!(top.map(|r| r.cell), Some(cell));
    t.info.remove(&cell);
    let canceled = t.canceled.remove(&cell);
    let ds = t.deps.remove(&cell).unwrap_or_default();
    if canceled {
        for &d in &ds {
            if is_running(d) || tasks().pending.contains_key(&d) {
                tasks().canceled.insert(d);
            }
        }
    }
    let t = tasks();
    for &d in &ds {
        if let Some(i) = t.info.get_mut(&d) {
            i.source = None;
        }
    }
    t.walks.push((cell, ds.into_iter().rev().collect()));
}

/// The next step of the walk of the dependents of the task that finished
/// last (`end`): a waiting `sync` dependent is handed to the caller, which
/// runs it (its tag is returned); the others are enqueued at their
/// priority. `u64::MAX` when the walk is over.
#[inline(never)]
pub fn walk_next() -> u64 {
    let t = tasks();
    loop {
        let Some((owner, frame)) = t.walks.last_mut() else { return u64::MAX };
        let owner = *owner;
        let Some(d) = frame.pop_front() else {
            t.walks.pop();
            // The worker that ran it is free once the walk is over.
            if t.worker == Some(owner) {
                worker_idle();
            }
            return u64::MAX;
        };
        let Some(e) = t.pending.get_mut(&d) else { continue };
        if !e.waiting {
            continue;
        }
        e.waiting = false;
        let tag = e.tag;
        let (prio, sync) = t.info.get(&d).map_or((0, false), |i| (i.prio, i.sync));
        if sync {
            t.pending.remove(&d);
            t.handed = Some(d);
            return tag;
        }
        let e = t.pending.get_mut(&d).unwrap();
        e.seq = t.next_seq;
        t.next_seq += 1;
        t.queues[prio].insert(e.seq, d);
    }
}

/// Before a task runs: if it waits for a pending task, which waits for
/// another, and so on, the deepest pending one of that chain is handed to
/// the caller, which runs it first (its tag is returned), so that a long
/// chain of dependents runs one task after the other instead of each
/// forcing its source recursively. `u64::MAX` when the task's source is
/// not pending.
#[inline(never)]
pub fn source_next(cell: usize) -> u64 {
    let t = tasks();
    if t.chains.last().map(|(c, _)| *c) != Some(cell) {
        // A new chain: the pending tasks `cell` waits for, transitively
        // (bounded: a bind task waiting for a task that depends on it is a
        // cycle).
        let mut chain = Vec::new();
        let mut c = cell;
        for _ in 0..=t.pending.len() {
            let Some(src) = t.info.get(&c).and_then(|i| i.source) else { break };
            if !t.pending.contains_key(&src) || src == cell {
                break;
            }
            chain.push(src);
            c = src;
        }
        if chain.is_empty() {
            return u64::MAX;
        }
        t.chains.push((cell, chain));
    }
    loop {
        let (_, chain) = t.chains.last_mut().unwrap();
        match chain.pop() {
            Some(d) => {
                let Some(e) = t.pending.get(&d) else { continue };
                let tag = e.tag;
                unqueue(d);
                tasks().handed = Some(d);
                return tag;
            }
            None => {
                t.chains.pop();
                return u64::MAX;
            }
        }
    }
}

/// The task handed over by `walk_next` or `source_next`, with the queue's
/// reference.
#[inline(never)]
pub fn handed() -> usize {
    tasks().handed.take().expect("leanrt: no task handed over")
}

/// A thread id for `IO.getTID`: natively a task runs on a worker thread, a
/// task waited for by a running task on another one. The id of the calling
/// thread plus the depth of nested running tasks.
#[inline(never)]
pub fn tid_offset() -> u64 {
    tasks().running.len() as u64
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

/// The next task of the final run of queued tasks: the first of the highest
/// non-empty priority queue (see `Tasks::queues`). When only tasks waiting
/// for others remain (a cycle), there is none: Lean's workers stop when the
/// queue is empty and leave such tasks behind.
fn next() -> Option<usize> {
    let t = tasks();
    if let Some(w) = t.worker {
        if t.pending.get(&w).is_some_and(|e| !e.waiting) {
            return Some(w);
        }
    }
    next_queued()
}

/// The first of the highest non-empty priority queue.
fn next_queued() -> Option<usize> {
    tasks().queues.iter().rev().find_map(|q| q.values().next().copied())
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
    unqueue(cell);
    cell
}

/// A thunk forced from its own computation, or tasks waiting for each other:
/// native Lean waits forever (without flushing stdout).
pub fn hang() -> ! {
    loop {
        std::thread::sleep(std::time::Duration::from_secs(3600));
    }
}
