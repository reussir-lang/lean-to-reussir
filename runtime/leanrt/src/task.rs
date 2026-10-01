//! Bookkeeping for deferred tasks.
//!
//! The runtime is single-threaded. A task is a runtime cell (`LCell`) whose
//! state lean2rr generates: `pending(action)`, `busy` or `done(value)` (and
//! a few more). After `main` has started, every new task is deferred: it
//! stays pending until the program first needs it, and otherwise runs when
//! `main` returns, like Lean's task manager, which finishes every queued
//! task before the process exits. Each such schedule is one a native thread
//! pool can produce (a worker may start a task at any time after it is
//! created). See translation plan §5.14.
//!
//! This module holds what the generated code cannot: an entry per
//! unfinished task (in a slab), the queues of pending tasks (one per
//! priority, in the order Lean's task manager enqueues them), each task's
//! dependents (an intrusive list, newest first, like Lean's `m_head_dep`),
//! the walk of a finished task's dependents, the stack of running tasks,
//! cancellation, the single native worker's state (which task it would
//! have started), and the phase of the program.
//!
//! A task is identified by the address of its cell. Its entry's index is
//! kept in the cell itself: an `LCell<S>` is a `reussir_rt::rc::Rc` of a
//! pointer-sized state, whose box is a 4-byte count, 4 bytes of padding and
//! the state, and the padding holds the index (`l2r_lcell_new` initializes
//! it to `NONE`; an index is valid when its entry records the same cell).
//! An entry lives until its task finishes (or is deleted): the address of a
//! finished task has no entry.
//!
//! References: the runtime holds one reference to the cell of every
//! deferred task that is pending (queued or waiting for another task), as
//! Lean's queue does for an IO task (`keep_alive`). A pure task (`Task.spawn`,
//! `Task.map`, `Task.bind`: `keep_alive = false`) is not kept alive natively:
//! when the program drops it before it has started, Lean deletes it. Here,
//! a pure task the runtime is about to start whose only reference is the
//! runtime's is deleted instead (handed to the generated code, which drops
//! it), also when the only other references come from pure dependents that
//! are dropped themselves (`dropped`).

use std::cell::UnsafeCell;
use std::collections::VecDeque;
use std::time::{Duration, Instant};

struct Global<T>(UnsafeCell<T>);
unsafe impl<T> Sync for Global<T> {}

/// No entry / end of a list.
pub const NONE: u32 = u32::MAX;

/// Priorities: Lean's 0..=8 (`Task.Priority.max`), and 9 for dedicated
/// tasks (a thread of their own natively, so started first here).
const PRIOS: usize = 10;

/// `kind` bits of `register`: a pure task (`keep_alive = false`), and a
/// dependent (`depend` follows and decides where it goes).
pub const K_PURE: u64 = 1;
pub const K_DEP: u64 = 2;

/// `begin` result bits: run with a stream context of its own (a worker
/// thread), and release the runtime's reference.
pub const B_ENTER: u64 = 1;
pub const B_RELEASE: u64 = 2;

// Entry flags.
/// `Task.spawn`/`map`/`bind`: deleted when dropped before it starts.
const PURE: u16 = 1 << 0;
/// Runs on the thread that finishes the task it waits for, as soon as that
/// one finishes (`sync := true`, or priority `LEAN_SYNC_PRIO`).
const SYNC: u16 = 1 << 1;
/// In its priority's queue.
const QUEUED: u16 = 1 << 2;
/// Waits for `source` (a dependent, or a bind task waiting for the task it
/// continues as); in that task's list of dependents.
const WAITING: u16 = 1 << 3;
const RUNNING: u16 = 1 << 4;
const CANCELED: u16 = 1 << 5;
/// Natively it could have started before `main` returned (see
/// `check_canceled`).
const EARLY: u16 = 1 << 6;
/// An unresolved promise: no computation, no reference held.
const PROMISE: u16 = 1 << 7;
/// The runtime holds one reference to the cell.
const HELD: u16 = 1 << 8;
/// Runs on the current thread when it begins (a `sync` dependent handed by
/// a walk, a task at priority `LEAN_SYNC_PRIO`): `thread` is set.
const INLINE: u16 = 1 << 9;
/// `IO.checkCanceled` was called in the current run.
const CHECKED: u16 = 1 << 10;
/// Priority `LEAN_SYNC_PRIO` (2^32-1): runs as soon as it is enqueued.
const SYNCPRIO: u16 = 1 << 11;
/// Handed to a walk's dispatcher: its own walk is left to that dispatcher.
const FROM_WALK: u16 = 1 << 12;
/// Running on the thread of whoever ran it (it began `INLINE`).
const ON_THREAD: u16 = 1 << 13;
/// Handed to the generated code to run (`hand`), not begun yet: it is off
/// its queue and its source's dependents, and no one else hands it (the
/// generated code may block before it begins, e.g. forcing its sources).
const HANDED: u16 = 1 << 14;

struct Entry {
    /// The cell's address; 0 for a free slot.
    cell: usize,
    /// Which generated state type the cell has (lean2rr's tag).
    tag: u32,
    flags: u16,
    prio: u8,
    /// Its dependents, newest first; its siblings in its source's list.
    head_dep: u32,
    next_dep: u32,
    prev_dep: u32,
    /// `QUEUED`: the sequence number of its queue item (stale items are
    /// skipped); `WAITING`: the task it waits for (its source).
    link: u32,
    /// Pending: `IO.getTaskState` reported it waiting (see `query`): the
    /// sleep count + 1 at the first such answer (0: never), and the number
    /// of answers. Running (or about to run `INLINE`): its thread number
    /// (0 is `main`'s), and the sleep count when the run started.
    aux: [u32; 2],
    /// The number of its allocation: an entry and a cell address are both
    /// reused once a task is gone, so a task remembered across a switch of
    /// contexts (`CtxState::chains`) is recognized by this.
    serial: u32,
}

impl Entry {
    #[inline]
    fn source(&self) -> u32 {
        self.link
    }
    #[inline]
    fn thread(&self) -> u32 {
        self.aux[0]
    }
    #[inline]
    fn start(&self) -> u32 {
        self.aux[1]
    }
}

const FREE: Entry = Entry {
    cell: 0, tag: 0, flags: 0, prio: 0, head_dep: NONE, next_dep: NONE, prev_dep: NONE, link: NONE, aux: [0, 0], serial: 0,
};

/// The dependents of a finished task still to be walked.
struct Walk {
    /// The finished task's entry, kept (without its cell) until the walk is
    /// over: its list of dependents is the walk's, newest first, as Lean's
    /// `handle_finished` walks them.
    owner: u32,
    /// The thread that finished the task (its `sync` dependents run there).
    thread: u32,
    /// The task finished before Lean's shutdown flag was set (natively).
    early: bool,
    canceled: bool,
    /// The worker is free once the walk is over (see `Tasks::worker`).
    worker: bool,
    /// The walk's own dispatcher stops at its end (otherwise the walk of a
    /// `sync` dependent, continued by the dispatcher of the enclosing walk).
    base: bool,
}

struct Tasks {
    /// `main` is running. Before (during module initialization) Lean has no
    /// task manager and runs every task at once.
    started: bool,
    /// `main` has returned; the remaining tasks run as during Lean's
    /// task-manager shutdown.
    shutting_down: bool,
    /// Sleeps so far (`IO.sleep`, `dbgSleep`): time passing, for the
    /// heuristics below.
    epoch: u32,
    slab: Vec<Entry>,
    free: Vec<u32>,
    /// Pending tasks that do not wait for another task, one queue per
    /// priority as in Lean's task manager (the highest non-empty one is
    /// taken first), in the order they were enqueued: (entry, sequence
    /// number).
    queues: [VecDeque<(u32, u32)>; PRIOS],
    /// The number of valid items of each queue.
    queued: [u32; PRIOS],
    next_q: u32,
    /// A task handed to the generated code (`walk_next`, `source_next`,
    /// `next_tag`), with the runtime's reference, to be run or, when
    /// `deleting`, dropped.
    handed: usize,
    deleting: bool,
    /// The task the single native worker (`LEAN_NUM_THREADS=1`) has started,
    /// still pending here: it runs first in the final run of queued tasks.
    /// An idle worker is woken by an enqueue (`wake`: when) and picks the
    /// first task of the highest non-empty queue once it has woken (a
    /// thread start, `LATENCY_COLD`, the first time, `LATENCY_WARM` later):
    /// tasks queued back to back compete by priority. When a task it ran
    /// finishes, it picks the next one right away.
    worker: u32,
    wake: Option<Instant>,
    worker_exists: bool,
    /// `IO.getTaskState` answered 4 (poll a promise) for this task: the
    /// `source_next` that follows does not wait for it for good.
    poll: usize,
    /// The last entry allocation's number (`Entry::serial`).
    serial: u32,
    /// Dropped pure tasks still to delete, the next one last, and the
    /// sources of tasks just deleted (`dropped`).
    deletions: Vec<u32>,
    recheck: Vec<u32>,
}

/// What belongs to the running context of the scheduler (`sched`), as
/// natively to a thread: the tasks running on it, the walks of dependents
/// in progress, and the chains of tasks being forced. A context that
/// blocks keeps its own (`swap_ctx_state`).
#[derive(Default)]
pub struct CtxState {
    /// Walks in progress, innermost last.
    walks: Vec<Walk>,
    /// For `source_next`: a task being forced (its cell and its entry's
    /// `serial`) and the pending tasks it waits for, still to run (entry
    /// and `serial`, deepest last), innermost last.
    chains: Vec<((usize, u32), Vec<(u32, u32)>)>,
    /// Running tasks (entries), innermost last.
    running: Vec<u32>,
}

static CTX: Global<CtxState> = Global(UnsafeCell::new(CtxState { walks: Vec::new(), chains: Vec::new(), running: Vec::new() }));

#[inline]
fn ctx() -> &'static mut CtxState {
    unsafe { &mut *CTX.0.get() }
}

/// Exchange the running context's state with `st` (`sched::switch_to`).
pub fn swap_ctx_state(st: &mut CtxState) {
    std::mem::swap(ctx(), st)
}

/// How long a native worker takes to pick up a task after the enqueue that
/// woke it: measured with `LEAN_NUM_THREADS=1` (a new thread: 80-100 µs;
/// an idle one: 15-20 µs).
const LATENCY_COLD: Duration = Duration::from_micros(90);
const LATENCY_WARM: Duration = Duration::from_micros(20);

static TASKS: Global<Tasks> = Global(UnsafeCell::new(Tasks {
    started: false,
    shutting_down: false,
    epoch: 0,
    slab: Vec::new(),
    free: Vec::new(),
    queues: [const { VecDeque::new() }; PRIOS],
    queued: [0; PRIOS],
    next_q: 0,
    handed: 0,
    deleting: false,
    worker: NONE,
    wake: None,
    worker_exists: false,
    poll: 0,
    serial: 0,
    deletions: Vec::new(),
    recheck: Vec::new(),
}));

#[inline]
fn tasks() -> &'static mut Tasks {
    unsafe { &mut *TASKS.0.get() }
}

/// The index slot in a cell (the box's padding, see the module comment).
#[inline]
fn slot(cell: usize) -> *mut u32 {
    (cell + 4) as *mut u32
}

/// The count of a cell (the box's first word).
#[inline]
fn count(cell: usize) -> u32 {
    unsafe { *(cell as *const u32) }
}

/// Initialize a new cell's index slot (`l2r_lcell_new`).
#[inline]
pub fn init_cell(cell: usize) {
    unsafe { *slot(cell) = NONE }
}

/// The entry of the task at `cell`, `NONE` if it has none (finished, or not
/// a deferred task).
#[inline]
fn find(cell: usize) -> u32 {
    let t = tasks();
    let i = unsafe { *slot(cell) };
    if (i as usize) < t.slab.len() && t.slab[i as usize].cell == cell { i } else { NONE }
}

#[inline]
fn ent(i: u32) -> &'static mut Entry {
    unsafe { tasks().slab.get_unchecked_mut(i as usize) }
}

fn alloc(cell: usize, tag: u32, flags: u16, prio: u8) -> u32 {
    let t = tasks();
    t.serial = t.serial.wrapping_add(1);
    let e = Entry { cell, tag, flags, prio, serial: t.serial, ..FREE };
    let i = match t.free.pop() {
        Some(i) => {
            t.slab[i as usize] = e;
            i
        }
        None => {
            t.slab.push(e);
            (t.slab.len() - 1) as u32
        }
    };
    unsafe { *slot(cell) = i };
    i
}

/// Remove entry `i` (unqueued, not waiting, no dependents left).
fn release(i: u32) {
    let e = ent(i);
    e.cell = 0;
    e.flags = 0;
    tasks().free.push(i);
}

/// The thread of the innermost running task (0: `main`).
#[inline]
fn cur_thread() -> u32 {
    match ctx().running.last() {
        Some(&r) => ent(r).thread(),
        None => crate::sched::cur_thread_base(),
    }
}

/// The thread number of the running task, or of the running context
/// (`sync`'s lock owners).
pub fn thread_now() -> u32 {
    cur_thread()
}

/// The entry point calls this right before `main`
/// (`lean_io_mark_end_initialization` + `lean_init_task_manager`).
pub fn start() {
    tasks().started = true;
}

/// Whether new tasks are deferred (otherwise they run at once).
#[inline]
pub fn deferring() -> bool {
    tasks().started
}

/// `main` has returned; the remaining tasks are about to run. The tasks
/// queued now could have been started by native workers before Lean's
/// shutdown flag was set (`EARLY`).
pub fn shutdown() {
    settle_worker();
    let t = tasks();
    t.shutting_down = true;
    for p in 0..PRIOS {
        for k in 0..t.queues[p].len() {
            let (i, q) = t.queues[p][k];
            let e = ent(i);
            if e.cell != 0 && e.flags & QUEUED != 0 && e.link == q {
                e.flags |= EARLY;
            }
        }
    }
}

/// `IO.sleep` / `dbgSleep`.
#[inline(never)]
pub fn sleep_ms(ms: u32) {
    settle_worker();
    tasks().epoch += 1;
    // Other contexts and queued tasks run meanwhile, as other threads
    // would (`sched::sleep`).
    if ms == 0 {
        std::thread::sleep(Duration::ZERO);
    } else {
        crate::sched::sleep(Duration::from_millis(ms as u64));
    }
    settle_worker();
}

/// Lean passes `lean_unbox(prio)` as an `unsigned`: the priority modulo
/// 2^32, where 2^32-1 is `LEAN_SYNC_PRIO` and above 8 is dedicated.
fn priority(prio: u64) -> (u8, bool) {
    let p = prio as u32;
    if p == u32::MAX { (0, true) } else { ((p as u64).min(PRIOS as u64 - 1) as u8, false) }
}

/// Whether running task `i` could still be running before Lean's shutdown
/// flag was set: it started early and no time has passed in it.
fn early_now(i: u32) -> bool {
    let t = tasks();
    let e = ent(i);
    t.shutting_down && e.flags & EARLY != 0 && e.flags & CHECKED == 0 && e.start() == t.epoch
}

/// A new deferred task at priority `prio` (Lean's `Task.Priority`, as
/// passed); the runtime takes over one reference to the cell. Returns 1 if
/// the caller must run it now, on the current thread (priority
/// `LEAN_SYNC_PRIO`, not a dependent: `enqueue_core` runs it at once).
#[inline(never)]
pub fn register(cell: usize, tag: u64, prio: u64, kind: u64) -> u64 {
    settle_worker();
    let (p, sp) = priority(prio);
    let mut flags = HELD;
    if kind & K_PURE != 0 {
        flags |= PURE;
    }
    if sp {
        flags |= SYNC | SYNCPRIO;
    }
    if let Some(&r) = ctx().running.last() {
        if early_now(r) {
            flags |= EARLY;
        }
    }
    let i = alloc(cell, tag as u32, flags, p);
    if kind & K_DEP != 0 {
        return 0;
    }
    if sp {
        run_here(i);
        return 1;
    }
    enqueue(i);
    0
}

/// Task `i` is to run on the current thread when it begins.
fn run_here(i: u32) {
    let th = cur_thread();
    let e = ent(i);
    e.flags |= INLINE;
    e.aux[0] = th;
}

/// Put pending task `i` at the end of its priority's queue.
fn enqueue(i: u32) {
    let t = tasks();
    let e = ent(i);
    e.flags |= QUEUED;
    t.next_q = t.next_q.wrapping_add(1);
    e.link = t.next_q;
    t.queues[e.prio as usize].push_back((i, e.link));
    t.queued[e.prio as usize] += 1;
    // An enqueue by `main` wakes the idle worker (if one is free: tasks
    // the scheduler started on contexts of their own hold workers).
    if t.started && !t.shutting_down && t.worker == NONE && t.wake.is_none() && ctx().running.is_empty()
        && crate::sched::cur() == crate::sched::MAIN
        && pool_in_use() < crate::sched::workers_limit()
    {
        t.wake = Some(Instant::now());
    }
    crate::sched::on_enqueue();
}

/// Take task `i` off its queue: its item is removed if it is at an end of
/// the queue (a task forced right after it was created), and becomes stale
/// otherwise (skipped later; the queue is compacted when they pile up).
fn unqueue(i: u32) {
    let e = ent(i);
    if e.flags & QUEUED != 0 {
        e.flags &= !QUEUED;
        let t = tasks();
        let p = e.prio as usize;
        t.queued[p] -= 1;
        let q = &mut t.queues[p];
        if q.back() == Some(&(i, e.link)) {
            q.pop_back();
        } else if q.front() == Some(&(i, e.link)) {
            q.pop_front();
        } else if q.len() > 64 && q.len() > 4 * t.queued[p] as usize {
            q.retain(|&(j, l)| {
                let f = ent(j);
                f.cell != 0 && f.flags & QUEUED != 0 && f.link == l
            });
        }
    }
}

/// Link task `d` at the head of `s`'s dependents.
fn link(s: u32, d: u32) {
    let h = ent(s).head_dep;
    let e = ent(d);
    e.link = s;
    e.next_dep = h;
    e.prev_dep = NONE;
    e.flags |= WAITING;
    if h != NONE {
        ent(h).prev_dep = d;
    }
    ent(s).head_dep = d;
}

/// Unlink waiting task `d` from its source's dependents.
fn unlink(d: u32) {
    let e = ent(d);
    if e.flags & WAITING == 0 {
        return;
    }
    let (s, n, p) = (e.source(), e.next_dep, e.prev_dep);
    if p != NONE {
        ent(p).next_dep = n;
    } else if s != NONE {
        ent(s).head_dep = n;
    }
    if n != NONE {
        ent(n).prev_dep = p;
    }
    let e = ent(d);
    e.link = NONE;
    e.next_dep = NONE;
    e.prev_dep = NONE;
    e.flags &= !WAITING;
}

/// `dep` (just registered with `K_DEP`) was created depending on `src`
/// (`sync`: with `sync := true`): if `src` is unfinished, `dep` waits for it
/// and runs or is enqueued when it finishes, as Lean's `add_dep`; otherwise
/// it is enqueued now. Returns 1 if the caller must run it now (priority
/// `LEAN_SYNC_PRIO` and `src` finished).
#[inline(never)]
pub fn depend(src: usize, dep: usize, sync: bool) -> u64 {
    let d = find(dep);
    if d == NONE {
        return 0;
    }
    if sync {
        ent(d).flags |= SYNC;
    }
    let s = find(src);
    if s != NONE {
        link(s, d);
        return 0;
    }
    if ent(d).flags & SYNCPRIO != 0 {
        run_here(d);
        return 1;
    }
    enqueue(d);
    0
}

/// The running `bind` task `cell` has run its function, which returned the
/// unfinished task `src`: it stops running and waits for `src` (keeping
/// its priority and flags), then continues as it (`task_bind_fn1` and
/// `run_task` re-adding it as a dependent). The runtime takes over one
/// reference to the cell.
#[inline(never)]
pub fn bind_wait(cell: usize, src: usize) {
    let i = find(cell);
    if ctx().running.last() == Some(&i) {
        ctx().running.pop();
    }
    let e = ent(i);
    e.flags &= !(RUNNING | INLINE | FROM_WALK | ON_THREAD | HANDED);
    e.flags |= HELD;
    e.aux = [0, 0];
    let s = find(src);
    if s != NONE {
        link(s, i);
    } else {
        enqueue(i);
    }
    if tasks().worker == i {
        worker_idle();
    }
}

/// A task starts running (`B_ENTER`: as a worker would, with streams of
/// its own; `B_RELEASE`: the caller must release the runtime's reference).
/// A cell without an entry is a converted task forwarding to its original:
/// it runs where it is forced.
#[inline(never)]
pub fn begin(cell: usize) -> u64 {
    let t = tasks();
    let mut i = find(cell);
    if i == NONE {
        i = alloc(cell, 0, INLINE, 0);
        ent(i).aux[0] = cur_thread();
    }
    let mut r = 0;
    let e = ent(i);
    if e.flags & HELD != 0 {
        r |= B_RELEASE;
    }
    unqueue(i);
    unlink(i);
    let e = ent(i);
    let mut on = ON_THREAD;
    if e.flags & INLINE == 0 {
        r |= B_ENTER;
        on = 0;
        e.aux[0] = cur_thread() + 1;
    }
    e.flags = (e.flags & !(HELD | INLINE | CHECKED | ON_THREAD | HANDED)) | RUNNING | on;
    e.aux[1] = t.epoch;
    ctx().running.push(i);
    r
}

/// The running task `cell` has finished: its dependents are to be walked
/// (`walk_next`), and canceled too if it was. Returns 1 if the caller must
/// walk them now (`l2r_task_walk`), 0 if the dispatcher that handed this
/// task over continues with them.
#[inline(never)]
pub fn end(cell: usize) -> u64 {
    let t = tasks();
    let Some(i) = ctx().running.pop() else { return 0 };
    debug_assert_eq!(ent(i).cell, cell);
    let early = early_now(i);
    let e = ent(i);
    let flags = e.flags;
    let thread = e.thread();
    // No longer found by its cell (finished); the entry stays for the walk.
    e.cell = 0;
    e.flags = 0;
    let base = flags & FROM_WALK == 0;
    // The worker that ran it picks the next task once the walk is over.
    let worker = t.worker == i
        || (t.worker == NONE && ctx().running.is_empty() && t.started && !t.shutting_down && flags & ON_THREAD == 0);
    if worker {
        t.worker = NONE;
        t.wake = None;
    }
    ctx().walks.push(Walk { owner: i, thread, early, canceled: flags & CANCELED != 0, worker, base });
    crate::sched::on_finish(cell);
    if base { 1 } else { 0 }
}

/// Promise `cell` has been resolved (its state is `done`): its dependents
/// are to be walked on the resolving thread. Returns 1 if the caller must
/// walk them (`l2r_task_walk`).
#[inline(never)]
pub fn resolve(cell: usize) -> u64 {
    let i = find(cell);
    if i == NONE || ent(i).flags & PROMISE == 0 {
        return 0;
    }
    let early = match ctx().running.last() {
        Some(&r) => early_now(r),
        None => false,
    };
    let e = ent(i);
    let canceled = e.flags & CANCELED != 0;
    e.cell = 0;
    e.flags = 0;
    let thread = cur_thread();
    ctx().walks.push(Walk { owner: i, thread, early, canceled, worker: false, base: true });
    crate::sched::on_finish(cell);
    1
}

/// An `IO.Promise`: the cell of its task, with one reference (natively the
/// promise holds one token of its task). Dropping the last reference to an
/// unresolved promise resolves it with `none` (Lean's `deactivate_promise`)
/// through the program's `l2r_promise_drop_c(cell)`, which also releases
/// the reference.
pub struct Promise {
    cell: usize,
}

extern "C" {
    /// lean2rr's `l2r_promise_drop(c : LCell<S>) -> u64` (one pointer
    /// argument, consumed), exported as `l2r_promise_drop_c` by programs
    /// that create promises.
    #[linkage = "extern_weak"]
    static l2r_promise_drop_c: *const std::ffi::c_void;
}

impl Drop for Promise {
    fn drop(&mut self) {
        let f = unsafe { l2r_promise_drop_c };
        assert!(!f.is_null(), "leanrt: promise without l2r_promise_drop_c");
        let f: unsafe extern "C" fn(usize) -> u64 = unsafe { std::mem::transmute(f) };
        unsafe { f(self.cell) };
    }
}

pub type LPromise = reussir_rt::rc::Rc<Box<dyn std::any::Any>>;

/// `IO.Promise.new`: a promise for the new unresolved task `cell` (whose
/// reference it takes). Before `main` Lean has no task manager, and
/// `lean_promise_new` reports an internal panic.
#[inline(never)]
pub fn promise_new(cell: usize) -> LPromise {
    if !tasks().started {
        crate::internal_panic(
            "`IO.Promise.new` called before the task manager is running; this typically happens when called (directly or transitively, e.g. via `IO.CancelToken.new`) from an `initialize` block. Construct lazily on first use instead.",
        );
    }
    alloc(cell, 0, PROMISE, 0);
    reussir_rt::rc::Rc::new(Box::new(Promise { cell }) as Box<dyn std::any::Any>)
}

/// The cell of promise `p`'s task (borrowed).
#[inline(never)]
pub fn promise_cell(p: &LPromise) -> usize {
    p.downcast_ref::<Promise>().expect("leanrt: not a promise").cell
}

/// Whether pending task `x` could be deleted rather than run: a pure task
/// the runtime holds, not running, not an unresolved promise, not started
/// by the worker.
fn deletable(x: u32) -> bool {
    let e = ent(x);
    e.flags & (PURE | HELD) == (PURE | HELD) && e.flags & (RUNNING | PROMISE) == 0 && tasks().worker != x
}

/// Whether pending task `x` is to be deleted now: a pure task that only
/// the runtime refers to (natively nothing refers to it any more, and Lean
/// has deleted it).
fn droppable_now(x: u32) -> bool {
    let e = ent(x);
    e.cell != 0 && deletable(x) && count(e.cell) == 1
}

/// The tasks to delete now among pending task `i` and the tasks that wait
/// for it, to any depth (an iterative search): those only the runtime
/// refers to, the ones deeper in the tree first. Deleting a task releases
/// what it holds (its source, directly or through a converted copy of it),
/// so its source may follow (`Tasks::recheck`): as natively, where
/// dropping the last reference to a dependent releases its source, a whole
/// chain or tree of dropped pure tasks is deleted.
///
/// The search goes only through tasks that could be deleted: one that
/// cannot (an IO task, a running one, a promise) holds its source for good,
/// so nothing below it can release `i`. Its own dropped dependents are
/// deleted when they come up (walked, or queued, once it has finished);
/// they cannot run before.
fn droppable_in(i: u32) -> Vec<u32> {
    let mut out = Vec::new();
    if !deletable(i) {
        return out;
    }
    // (task, its next dependent to look at)
    let mut stack: Vec<(u32, u32)> = vec![(i, ent(i).head_dep)];
    // Each task once (a bound, for tasks that wait for each other in a
    // cycle).
    let mut budget = 2 * tasks().slab.len() + 2;
    while let Some(top) = stack.last_mut() {
        if budget == 0 {
            break;
        }
        budget -= 1;
        let d = top.1;
        if d != NONE {
            top.1 = ent(d).next_dep;
            if deletable(d) {
                stack.push((d, ent(d).head_dep));
            }
        } else {
            let (x, _) = stack.pop().unwrap();
            if droppable_now(x) {
                out.push(x);
            }
        }
    }
    out
}

/// Whether pending task `i` is to be deleted, or tasks waiting for it are,
/// before it can be decided whether it runs.
fn is_dropped(i: u32) -> bool {
    !droppable_in(i).is_empty()
}

/// The next task to delete: the source of a task just deleted, if only
/// the runtime refers to it now, one left by an earlier search, or the
/// first of those found among `i` and the tasks that wait for it (the
/// others are left for the next calls); `NONE` if there is none (`i` is to
/// run).
fn dropped(i: u32) -> u32 {
    let t = tasks();
    while let Some(x) = t.recheck.pop() {
        if droppable_now(x) {
            return x;
        }
    }
    while let Some(x) = t.deletions.pop() {
        if droppable_now(x) {
            return x;
        }
    }
    let mut v = droppable_in(i);
    if v.is_empty() {
        return NONE;
    }
    v.reverse();
    let first = v.pop().unwrap();
    tasks().deletions = v;
    first
}

/// Hand pending task `i` to the generated code (with the runtime's
/// reference), to run it or (`del`) drop it; returns its tag.
fn hand(i: u32, del: bool) -> u64 {
    let t = tasks();
    unqueue(i);
    let e = ent(i);
    let tag = e.tag as u64;
    t.handed = e.cell;
    t.deleting = del;
    if del {
        // Its source may only be referred to by the runtime once this one
        // is dropped.
        if e.flags & WAITING != 0 && e.source() != NONE {
            t.recheck.push(e.source());
        }
        unlink(i);
        // Its own (deleted) dependents went first.
        debug_assert_eq!(ent(i).head_dep, NONE);
        release(i);
    } else {
        unlink(i);
        let e = ent(i);
        e.flags = (e.flags & !HELD) | HANDED;
    }
    tag
}

/// The next step of the walk of the dependents of the task that finished
/// last (`end`): a `sync` dependent is handed to the caller, which runs it
/// on the finishing thread (its tag is returned; dropped pure ones are
/// handed to be dropped); the others are enqueued at their priority.
/// `u64::MAX` when the walk is over.
#[inline(never)]
pub fn walk_next() -> u64 {
    loop {
        let Some(f) = ctx().walks.last() else { return u64::MAX };
        let (owner, thread, early, canceled) = (f.owner, f.thread, f.early, f.canceled);
        let d = ent(owner).head_dep;
        if d == NONE {
            let f = ctx().walks.pop().unwrap();
            release(owner);
            if f.worker {
                worker_idle();
            }
            if f.base {
                return u64::MAX;
            }
            continue;
        }
        let e = ent(d);
        if e.flags & SYNC != 0 && e.flags & PURE != 0 {
            let x = dropped(d);
            if x != NONE {
                // `d` itself, or first a dependent of `d` holding it.
                return hand(x, true);
            }
        }
        unlink(d);
        let e = ent(d);
        if canceled {
            e.flags |= CANCELED;
        }
        if early {
            e.flags |= EARLY;
        }
        if e.flags & SYNC != 0 {
            e.flags |= INLINE | FROM_WALK;
            e.aux[0] = thread;
            return hand(d, false);
        }
        enqueue(d);
    }
}

/// The next queued task to run (the worker's started one first, then the
/// first of the highest non-empty queue), handed over with its tag (or a
/// dropped pure task to delete); `u64::MAX` if none.
///
/// For a worker context of the scheduler, its first task (`sched`). After
/// `main` has returned (the final run, on `main`'s context), a task starts
/// only when a worker would be free for it (`startable`); otherwise, and
/// while tasks started on other contexts are still running, `main` waits.
/// When only tasks waiting for others remain (a cycle), there is none:
/// Lean's workers stop when the queue is empty and leave such tasks behind.
#[inline(never)]
pub fn next_tag() -> u64 {
    let p = crate::sched::take_preselect();
    if p != NONE {
        return hand_candidate(p);
    }
    let t = tasks();
    if t.shutting_down && crate::sched::cur() == crate::sched::MAIN && ctx().running.is_empty() {
        loop {
            let e = startable(true);
            if e != NONE {
                return hand_candidate(e);
            }
            if !has_queued() && !crate::sched::workers_alive() {
                return u64::MAX;
            }
            crate::sched::block(crate::sched::Wait::FinalRun);
        }
    }
    let w = t.worker;
    let cand = if w != NONE && ent(w).flags & QUEUED != 0 { w } else { first_queued() };
    if cand == NONE {
        return u64::MAX;
    }
    hand_candidate(cand)
}

/// Hand queued task `cand` over to be run, or the dropped pure task it
/// stands for to be deleted (`dropped`).
fn hand_candidate(cand: u32) -> u64 {
    let e = ent(cand);
    if e.cell == 0 || e.flags & QUEUED == 0 {
        // Started or deleted meanwhile.
        return u64::MAX;
    }
    if cand != tasks().worker {
        let x = dropped(cand);
        if x != NONE {
            return hand(x, true);
        }
    }
    hand(cand, false)
}

/// Whether tasks are queued.
pub fn has_queued() -> bool {
    first_queued() != NONE
}

/// The queued task the scheduler can start now on a new context (or a
/// worker context that has finished its task, `from_worker`, which holds no
/// worker then): the one `next_tag` would hand over, if a worker is free
/// for it. Natively a task at a priority up to `Task.Priority.max` waits
/// for one of the task manager's workers (`LEAN_NUM_THREADS`, or one per
/// processor); a worker waiting for a task (`IO.wait`, `Task.get`) frees
/// its place meanwhile (`wait_for`); a dedicated task has a thread of its
/// own. `NONE` if none.
pub fn startable(from_worker: bool) -> u32 {
    let t = tasks();
    if !t.started {
        return NONE;
    }
    let _ = from_worker;
    settle_worker();
    let w = t.worker;
    let cand = if w != NONE && ent(w).flags & QUEUED != 0 { w } else { first_queued() };
    if cand == NONE {
        return NONE;
    }
    if cand != w && (!t.deletions.is_empty() || !t.recheck.is_empty() || is_dropped(cand)) {
        // Deleting it needs no worker.
        return cand;
    }
    if ent(cand).prio as usize == PRIOS - 1 {
        return cand;
    }
    if pool_in_use() < crate::sched::workers_limit() { cand } else { NONE }
}

/// Whether a context with this bookkeeping holds one of the task manager's
/// workers: the innermost task running on it (not on the thread of whoever
/// ran it) is at a pool priority, and it is not waiting for a task.
fn holds_worker(st: &CtxState, w: crate::sched::Wait) -> bool {
    use crate::sched::Wait;
    if matches!(w, Wait::Cell(_) | Wait::CellPoll(_) | Wait::Progress) {
        return false;
    }
    for &i in st.running.iter().rev() {
        let e = ent(i);
        if e.flags & ON_THREAD != 0 {
            continue;
        }
        return (e.prio as usize) < PRIOS - 1;
    }
    false
}

/// The number of the task manager's workers in use.
fn pool_in_use() -> u32 {
    let mut n = if holds_worker(ctx(), crate::sched::cur_wait()) { 1 } else { 0 };
    crate::sched::for_each_other(|st, w| {
        if holds_worker(st, w) {
            n += 1
        }
    });
    n
}

/// A `busy` task (`Task.get` of a task that is running): it runs on
/// another context, which has blocked; wait until it has finished. On the
/// running context it needs itself: native Lean waits forever then.
#[inline(never)]
pub fn wait_running(a: usize) -> u64 {
    let i = find(a);
    if i == NONE {
        return 1;
    }
    if ctx().running.contains(&i) {
        hang();
    }
    crate::sched::block(crate::sched::Wait::Cell(a));
    1
}

/// `IO.waitAny` when every task of the list is running or waits for a
/// promise: wait until some task finishes (other contexts and queued tasks
/// run meanwhile), then the list is looked at again.
#[inline(never)]
pub fn wait_progress() -> u64 {
    crate::sched::block(crate::sched::Wait::Progress);
    1
}

/// The first valid item of the highest non-empty queue (stale items in
/// front are discarded).
fn first_queued() -> u32 {
    let t = tasks();
    for p in (0..PRIOS).rev() {
        if t.queued[p] == 0 {
            continue;
        }
        while let Some(&(i, q)) = t.queues[p].front() {
            let e = ent(i);
            if e.cell != 0 && e.flags & QUEUED != 0 && e.link == q {
                return i;
            }
            t.queues[p].pop_front();
        }
    }
    NONE
}

/// What the idle worker picks: the first task of the highest non-empty
/// queue that is not a dropped pure task (natively deleted already).
fn pick() -> u32 {
    let t = tasks();
    for p in (0..PRIOS).rev() {
        if t.queued[p] == 0 {
            continue;
        }
        for k in 0..t.queues[p].len() {
            let (i, q) = t.queues[p][k];
            let e = ent(i);
            if e.cell != 0 && e.flags & QUEUED != 0 && e.link == q && !is_dropped(i) {
                return i;
            }
        }
    }
    NONE
}

/// The worker is free: it starts the next queued task, if any.
fn worker_idle() {
    let t = tasks();
    t.wake = None;
    t.worker = if t.started && !t.shutting_down && pool_in_use() < crate::sched::workers_limit() { pick() } else { NONE };
}

/// The woken worker has picked its task if enough time has passed.
fn settle_worker() {
    let t = tasks();
    if let Some(w) = t.wake {
        let lat = if t.worker_exists { LATENCY_WARM } else { LATENCY_COLD };
        if w.elapsed() >= lat {
            t.worker_exists = true;
            worker_idle();
        }
    }
}

/// Before a task runs: if it waits for a pending task, which waits for
/// another, and so on, the deepest pending one of that chain is handed to
/// the caller, which runs it first (its tag is returned), so that a long
/// chain of dependents runs one task after the other instead of each
/// forcing its source recursively. When the chain ends at an unresolved
/// promise (or the task is one), queued tasks are handed instead, one at a
/// time, until it is resolved: natively a worker runs them meanwhile, and
/// one may resolve it. `u64::MAX` when there is nothing (more) to run.
#[inline(never)]
pub fn source_next(cell: usize) -> u64 {
    let t = tasks();
    let i = find(cell);
    let key = (cell, if i == NONE { 0 } else { ent(i).serial });
    if ctx().chains.last().map(|(k, _)| *k) != Some(key) {
        // A new chain: the pending tasks `cell` waits for, transitively
        // (bounded: a bind task waiting for a task that depends on it is a
        // cycle). Chains run to their end were left behind by forcing that
        // has finished.
        while ctx().chains.last().is_some_and(|(_, c)| c.is_empty()) {
            ctx().chains.pop();
        }
        if i == NONE {
            return u64::MAX;
        }
        let mut chain = Vec::new();
        if ent(i).flags & PROMISE != 0 {
            chain.push((i, ent(i).serial));
        } else {
            let mut c = i;
            for _ in 0..=t.slab.len() {
                let s = ent(c).source();
                if ent(c).flags & WAITING == 0 || s == NONE || s == i || ent(s).flags & (RUNNING | HANDED) != 0 {
                    break;
                }
                chain.push((s, ent(s).serial));
                if ent(s).flags & PROMISE != 0 {
                    break;
                }
                c = s;
            }
        }
        if chain.is_empty() {
            return u64::MAX;
        }
        ctx().chains.push((key, chain));
    }
    loop {
        let (_, chain) = ctx().chains.last_mut().unwrap();
        let Some(&(d, sr)) = chain.last() else {
            ctx().chains.pop();
            return u64::MAX;
        };
        let e = ent(d);
        if e.cell == 0 || e.serial != sr || e.flags & (RUNNING | HANDED) != 0 {
            // Finished (or started, or handed to another) meanwhile; its
            // entry may hold another task since.
            chain.pop();
            continue;
        }
        let c = e.cell;
        if e.flags & PROMISE != 0 {
            // Wait until it is resolved (other contexts and queued tasks
            // run meanwhile, as other threads would). A program polling
            // for it (`query` answered 4) goes on once nothing else can.
            let poll = std::mem::replace(&mut tasks().poll, 0) == cell;
            crate::sched::block(if poll { crate::sched::Wait::CellPoll(c) } else { crate::sched::Wait::Cell(c) });
            if poll {
                ctx().chains.pop();
                return u64::MAX;
            }
            continue;
        }
        chain.pop();
        return hand(d, false);
    }
}

/// The task handed over by `walk_next`, `source_next` or `next_tag`, with
/// the runtime's reference.
#[inline(never)]
pub fn handed() -> usize {
    let t = tasks();
    let c = t.handed;
    assert!(c != 0, "leanrt: no task handed over");
    t.handed = 0;
    c
}

/// Whether the task handed over is to be dropped (a pure task the program
/// has dropped before it started) rather than run.
#[inline]
pub fn deleting() -> bool {
    tasks().deleting
}

/// A thread id for `IO.getTID`: natively a task runs on a worker thread, a
/// task waited for by a running task on another one, a `sync` dependent on
/// the thread that finished its source. The id of the calling thread plus
/// this number.
#[inline(never)]
pub fn tid_offset() -> u64 {
    cur_thread() as u64
}

/// The state of a task: 0 waiting (pending), 1 running (or an unresolved
/// promise, as natively), 2 finished.
#[inline(never)]
pub fn status(cell: usize) -> u8 {
    let i = find(cell);
    if i == NONE {
        return 2;
    }
    if ent(i).flags & (RUNNING | PROMISE | HANDED) != 0 { 1 } else { 0 }
}

/// For `IO.waitAny`: as `status`, or 3 for a pending task that waits,
/// directly or through other pending tasks, for an unresolved promise
/// (running it would wait for the promise).
#[inline(never)]
pub fn wait_status(cell: usize) -> u8 {
    let t = tasks();
    let i = find(cell);
    if i == NONE {
        return 2;
    }
    if ent(i).flags & (RUNNING | PROMISE) != 0 {
        return 1;
    }
    let mut c = i;
    for _ in 0..t.slab.len() {
        if ent(c).flags & WAITING == 0 {
            break;
        }
        c = ent(c).source();
        if ent(c).flags & PROMISE != 0 {
            return 3;
        }
        if ent(c).flags & (RUNNING | HANDED) != 0 {
            break;
        }
    }
    0
}

/// `IO.getTaskState`: as `status`, or 3: the caller runs the task and
/// reports it finished, or 4 (an unresolved promise): the caller runs
/// queued tasks until it is resolved or none is left, and reports its state
/// then. A pending task is reported waiting until the program asks again
/// after some time has passed (a sleep) or keeps asking (a busy loop): it
/// is then polling for the task, which a worker would have run meanwhile.
#[inline(never)]
pub fn query(cell: usize) -> u8 {
    let t = tasks();
    let i = find(cell);
    if i == NONE {
        return 2;
    }
    let e = ent(i);
    if e.flags & (RUNNING | HANDED) != 0 {
        return 1;
    }
    let idle = if e.flags & PROMISE != 0 { 1 } else { 0 };
    let poll = if e.flags & PROMISE != 0 { 4 } else { 3 };
    let [observed, queries] = e.aux;
    if observed == 0 {
        e.aux = [t.epoch + 1, 1];
        return idle;
    }
    if t.epoch + 1 > observed || queries >= 1000 {
        // The next question starts over (a promise may stay unresolved).
        e.aux = [0, 0];
        if poll == 4 {
            t.poll = cell;
        }
        if poll == 3 && wait_status(cell) == 3 {
            // It waits for an unresolved promise: running it would wait
            // for the promise. Other contexts and queued tasks run
            // meanwhile, as other threads would, until it has finished or
            // nothing else can go on; its state then.
            crate::sched::block(crate::sched::Wait::CellPoll(cell));
            return status(cell);
        }
        return poll;
    }
    e.aux[1] += 1;
    idle
}

/// `IO.Promise.isResolved` (lean2rr's shim, `L2RShim.promiseIsResolved`):
/// `IO.hasFinished` of the promise's task, as `IO.getTaskState` answers it
/// (`query`; when it answers 4, the program polls: other contexts and
/// queued tasks run first, until the promise is resolved or nothing else
/// can go on). The caller releases the promise afterwards: natively
/// `isResolved` borrows it, so a last reference is dropped (resolving the
/// promise with `none`) only after the question.
#[inline(never)]
pub fn promise_is_resolved(cell: usize) -> bool {
    match query(cell) {
        2 => true,
        4 => {
            source_next(cell);
            status(cell) == 2
        }
        _ => false,
    }
}

/// `IO.cancel` of a task.
#[inline(never)]
pub fn cancel(cell: usize) {
    let i = find(cell);
    if i != NONE {
        ent(i).flags |= CANCELED;
    }
}

/// `IO.checkCanceled`: inside a task, whether it was canceled or the program
/// is shutting down; always false in `main`. At shutdown, Lean sets its flag
/// while the remaining tasks run. A task that could have started before
/// (queued when `main` returned, or created or released by such a task
/// still in its first moments) sees it once time has passed in it (a sleep)
/// or from its second check on; any other task (it could only start after
/// its source finished, or did not exist yet) sees it at once.
#[inline(never)]
pub fn check_canceled() -> bool {
    let t = tasks();
    let Some(&i) = ctx().running.last() else { return false };
    let late = if t.shutting_down {
        let late = !early_now(i);
        ent(i).flags |= CHECKED;
        late
    } else {
        false
    };
    late || ent(i).flags & CANCELED != 0
}

/// A thunk forced from its own computation, or tasks waiting for each other:
/// native Lean waits forever (without flushing stdout).
pub fn hang() -> ! {
    // Other contexts go on meanwhile, as other threads would.
    if tasks().started {
        loop {
            crate::sched::block(crate::sched::Wait::Forever);
        }
    }
    hang_thread()
}

/// Wait forever: nothing can go on any more.
pub fn hang_thread() -> ! {
    loop {
        std::thread::sleep(std::time::Duration::from_secs(3600));
    }
}

#[cfg(test)]
mod tests {
    use super::priority;

    #[test]
    fn priorities() {
        assert_eq!(priority(0), (0, false));
        assert_eq!(priority(8), (8, false));
        assert_eq!(priority(9), (9, false));
        assert_eq!(priority(1000), (9, false));
        assert_eq!(priority(4294967295), (0, true));
        assert_eq!(priority(4294967297), (1, false));
        assert_eq!(priority(8589934596), (4, false));
    }
}
