//! The scheduler: contexts that block and resume, on one thread.
//!
//! Native Lean runs tasks on a pool of worker threads (and `main` on its own
//! thread); a thread that blocks on a mutex, a condition variable, a task or
//! promise that has not finished, or a sleep lets the others go on. The
//! translation runs on one thread, so it has *contexts* instead (`coro`):
//! `main`'s (the thread's own stack) and one per task the scheduler starts,
//! each on a stack of its own. A task that is needed (`Task.get`,
//! `IO.wait`) still runs right there, on the stack of whoever needs it
//! (translation plan §5.14); a context switch happens only when the running
//! context blocks:
//!
//! - it waits for a task that runs on another context, or for a promise;
//! - it waits for a mutex another context holds, or on a condition
//!   variable;
//! - it sleeps (`IO.sleep`);
//! - after `main` has returned, it waits for the remaining tasks.
//!
//! The scheduler then runs, in this order: a context that can go on (in the
//! order they became able to), else a queued task on a new context (in the
//! order Lean's task manager would start it, within its number of workers:
//! `LEAN_NUM_THREADS`, or the number of processors; a task at
//! `Task.Priority.dedicated` has a thread of its own natively and always
//! starts), else whatever the event loop is waiting for (`net`: timers,
//! sockets) or the earliest sleeper, waiting for it. When nothing can ever
//! go on, the program waits forever, as natively a deadlocked one does.
//!
//! A context that blocks keeps its own task bookkeeping (`task::CtxState`:
//! the running tasks, walks of dependents, chains being forced) and its own
//! standard streams (`once::CtxState`), as a thread keeps its own; the
//! switch saves the leaving context's and restores the arriving one's.

use crate::coro::Stack;
use std::cell::UnsafeCell;
use std::collections::{HashMap, VecDeque};
use std::time::{Duration, Instant};

struct Global<T>(UnsafeCell<T>);
unsafe impl<T> Sync for Global<T> {}

pub type CtxId = u32;
/// `main`'s context (also the one of the initializers before it).
pub const MAIN: CtxId = 0;

/// What a blocked context waits for.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Wait {
    None,
    /// The task or promise with this identity finishes.
    Cell(usize),
    /// The same, for a program polling it (`IO.getTaskState`): also woken
    /// when nothing else can go on.
    CellPoll(usize),
    /// Any task finishes (`IO.waitAny` when every task is running).
    Progress,
    /// `main` has returned and waits for the remaining tasks: woken when a
    /// context ends, a task finishes or is queued.
    FinalRun,
    /// A synchronization object (`sync`): woken by whoever hands it over.
    Sync(usize),
    /// A sleep until the deadline.
    Sleep(Instant),
    /// The event loop's context waits for timers and sockets (`net`).
    Io,
    /// Nothing: a context that waits forever (a task needed by its own
    /// computation; natively the thread waits forever, the others go on).
    Forever,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Status {
    Running,
    Runnable,
    Blocked,
    Dead,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Kind {
    Main,
    /// Runs queued tasks, as a worker thread.
    Worker,
    /// The event loop (`net`), as libuv's thread.
    EvLoop,
}

struct Ctx {
    status: Status,
    wait: Wait,
    kind: Kind,
    /// The saved stack pointer while not running.
    sp: usize,
    stack: Option<Stack>,
    /// The thread number of tasks running on it outside of any other task
    /// (`task::cur_thread`): 0 for `main`'s.
    thread_base: u32,
    tasks: crate::task::CtxState,
    once: crate::once::CtxState,
    /// A worker's first task (`task::next_tag` hands it over).
    preselect: u32,
}

impl Ctx {
    fn new(kind: Kind, thread_base: u32) -> Ctx {
        Ctx {
            status: Status::Runnable,
            wait: Wait::None,
            kind,
            sp: 0,
            stack: None,
            thread_base,
            tasks: Default::default(),
            once: Default::default(),
            preselect: crate::task::NONE,
        }
    }
}

struct Sched {
    ctxs: Vec<Ctx>,
    free: Vec<CtxId>,
    cur: CtxId,
    /// Contexts that can go on, in the order they became able to.
    runnable: VecDeque<CtxId>,
    /// Sleeping contexts and their deadlines.
    sleepers: Vec<(Instant, CtxId)>,
    /// Contexts waiting for a task or promise, by its identity.
    cell_waiters: HashMap<usize, Vec<CtxId>>,
    /// Contexts waiting for any task to finish (`Wait::Progress`,
    /// `Wait::FinalRun`).
    progress_waiters: Vec<CtxId>,
    /// Blocked contexts (all reasons).
    blocked: u32,
    /// Live worker contexts.
    workers: u32,
    /// A context that has ended, whose stack is freed by the next one to
    /// run (it cannot free the stack it runs on).
    zombie: Option<Stack>,
    evloop: Option<CtxId>,
    pool_limit: u32,
    next_thread: u32,
    /// Free stacks for new contexts.
    pool: Vec<Stack>,
}

static SCHED: Global<Option<Sched>> = Global(UnsafeCell::new(None));

#[inline]
fn sched() -> &'static mut Sched {
    let s = unsafe { &mut *SCHED.0.get() };
    if s.is_none() {
        init(s);
    }
    s.as_mut().unwrap()
}

#[cold]
fn init(s: &mut Option<Sched>) {
    let mut main = Ctx::new(Kind::Main, 0);
    main.status = Status::Running;
    *s = Some(Sched {
        ctxs: vec![main],
        free: Vec::new(),
        cur: MAIN,
        runnable: VecDeque::new(),
        sleepers: Vec::new(),
        cell_waiters: HashMap::new(),
        progress_waiters: Vec::new(),
        blocked: 0,
        workers: 0,
        zombie: None,
        evloop: None,
        pool_limit: pool_limit(),
        next_thread: 1,
        pool: Vec::new(),
    });
}

/// The number of worker threads of Lean's task manager:
/// `LEAN_NUM_THREADS` (C's `atoi`), or the number of processors.
fn pool_limit() -> u32 {
    if let Some(v) = std::env::var_os("LEAN_NUM_THREADS") {
        let s = std::os::unix::ffi::OsStrExt::as_bytes(v.as_os_str());
        let mut i = 0;
        while i < s.len() && matches!(s[i], b' ' | b'\t' | b'\n' | b'\x0b' | b'\x0c' | b'\r') {
            i += 1;
        }
        let neg = i < s.len() && s[i] == b'-';
        if i < s.len() && (s[i] == b'-' || s[i] == b'+') {
            i += 1;
        }
        let mut n: i64 = 0;
        while i < s.len() && s[i].is_ascii_digit() {
            n = n.wrapping_mul(10).wrapping_add((s[i] - b'0') as i64);
            i += 1;
        }
        let n = if neg { -n } else { n } as i32;
        return if n <= 0 { 1 } else { n as u32 };
    }
    std::thread::available_parallelism().map(|n| n.get() as u32).unwrap_or(1)
}

/// The running context.
#[inline]
pub fn cur() -> CtxId {
    let s = unsafe { &*SCHED.0.get() };
    match s {
        Some(s) => s.cur,
        None => MAIN,
    }
}

/// The kind of the running context.
pub fn cur_kind() -> Kind {
    let s = sched();
    s.ctxs[s.cur as usize].kind
}

/// Whether contexts other than the running one exist (alive).
#[inline]
pub fn others_alive() -> bool {
    let s = unsafe { &*SCHED.0.get() };
    match s {
        Some(s) => s.ctxs.len() - s.free.len() > 1,
        None => false,
    }
}

/// Whether some context waits for something (fast check for the hooks).
#[inline]
fn any_blocked() -> bool {
    let s = unsafe { &*SCHED.0.get() };
    match s {
        Some(s) => s.blocked > 0,
        None => false,
    }
}

/// The thread number of the running context's own tasks.
#[inline]
pub fn cur_thread_base() -> u32 {
    let s = unsafe { &*SCHED.0.get() };
    match s {
        Some(s) => s.ctxs[s.cur as usize].thread_base,
        None => 0,
    }
}

/// The number of worker threads (`pool_limit`).
pub fn workers_limit() -> u32 {
    sched().pool_limit
}

/// A worker's first task, once (see `task::next_tag`).
pub fn take_preselect() -> u32 {
    let s = sched();
    let c = &mut s.ctxs[s.cur as usize];
    std::mem::replace(&mut c.preselect, crate::task::NONE)
}

/// Visit the task bookkeeping of every live context other than the running
/// one, with what it waits for (the running context's is the global one).
pub fn for_each_other(mut f: impl FnMut(&crate::task::CtxState, Wait)) {
    let s = sched();
    for (i, c) in s.ctxs.iter().enumerate() {
        if i as CtxId != s.cur && c.status != Status::Dead {
            f(&c.tasks, c.wait);
        }
    }
}

/// What the running context waits for (`Wait::None` while it runs).
pub fn cur_wait() -> Wait {
    let s = sched();
    s.ctxs[s.cur as usize].wait
}

/// Block the running context until it is woken (`wake`) for `w`; other
/// contexts run meanwhile. Returns once it runs again.
pub fn block(w: Wait) {
    let s = sched();
    let c = s.cur;
    {
        let x = &mut s.ctxs[c as usize];
        debug_assert_eq!(x.status, Status::Running);
        x.status = Status::Blocked;
        x.wait = w;
    }
    s.blocked += 1;
    match w {
        Wait::Cell(a) | Wait::CellPoll(a) => s.cell_waiters.entry(a).or_default().push(c),
        Wait::Progress | Wait::FinalRun => s.progress_waiters.push(c),
        Wait::Sleep(d) => s.sleepers.push((d, c)),
        _ => {}
    }
    schedule();
}

/// Let other contexts that can go on run first (the running one goes on
/// after them).
pub fn yield_now() {
    let s = sched();
    let c = s.cur;
    s.ctxs[c as usize].status = Status::Runnable;
    s.runnable.push_back(c);
    schedule();
}

/// Make blocked context `c` able to go on.
pub fn wake(c: CtxId) {
    let s = sched();
    let x = &mut s.ctxs[c as usize];
    if x.status == Status::Blocked {
        x.status = Status::Runnable;
        x.wait = Wait::None;
        s.blocked -= 1;
        s.runnable.push_back(c);
    }
}

/// A task or promise with identity `a` has finished: wake whoever waits
/// for it or for any task.
#[inline]
pub fn on_finish(a: usize) {
    if any_blocked() {
        on_finish_slow(a)
    }
}

#[inline(never)]
fn on_finish_slow(a: usize) {
    let s = sched();
    if let Some(ws) = s.cell_waiters.remove(&a) {
        for c in ws {
            if matches!(s.ctxs[c as usize].wait, Wait::Cell(x) | Wait::CellPoll(x) if x == a) {
                wake(c);
            }
        }
    }
    wake_progress();
}

/// Something changed that `Wait::Progress`/`Wait::FinalRun` waiters look
/// at: a task finished or was queued, a context ended.
fn wake_progress() {
    let s = sched();
    if s.progress_waiters.is_empty() {
        return;
    }
    let ws = std::mem::take(&mut s.progress_waiters);
    for c in ws {
        if matches!(s.ctxs[c as usize].wait, Wait::Progress | Wait::FinalRun) {
            wake(c);
        }
    }
}

/// A task was queued.
#[inline]
pub fn on_enqueue() {
    if any_blocked() {
        wake_progress()
    }
}

/// Sleep for `d` (`IO.sleep`): the running context blocks until then, and
/// others run meanwhile. Without anything else to do, a plain sleep.
pub fn sleep(d: Duration) {
    let s = sched();
    let alone = s.ctxs.len() - s.free.len() == 1 && s.evloop.is_none() && !crate::task::has_queued();
    if alone || !crate::task::deferring() {
        std::thread::sleep(d);
        return;
    }
    block(Wait::Sleep(Instant::now() + d));
}

/// Wake the sleepers whose deadline has passed (in deadline order, as
/// their threads would wake); the earliest deadline left.
fn promote_sleepers(now: Instant) -> Option<Instant> {
    let s = sched();
    if s.sleepers.is_empty() {
        return None;
    }
    let mut next: Option<Instant> = None;
    let mut due: Vec<(Instant, CtxId)> = Vec::new();
    let mut i = 0;
    while i < s.sleepers.len() {
        let (d, c) = s.sleepers[i];
        let x = &s.ctxs[c as usize];
        if x.status != Status::Blocked || x.wait != Wait::Sleep(d) {
            s.sleepers.swap_remove(i);
            continue;
        }
        if d <= now {
            s.sleepers.swap_remove(i);
            due.push((d, c));
            continue;
        }
        next = Some(next.map_or(d, |n| n.min(d)));
        i += 1;
    }
    due.sort();
    for (_, c) in due {
        wake(c);
    }
    next
}

/// Whether a sleeper's deadline has passed (for effect points).
pub fn sleeper_due(now: Instant) -> bool {
    let s = sched();
    s.sleepers.iter().any(|&(d, c)| d <= now && s.ctxs[c as usize].wait == Wait::Sleep(d))
}

/// An observable effect (output) of the running context: a context whose
/// sleep has ended meanwhile would natively have run by now, so it goes
/// first.
#[inline]
pub fn effect() {
    let s = unsafe { &*SCHED.0.get() };
    if let Some(s) = s {
        if !s.sleepers.is_empty() || s.evloop.is_some() {
            effect_slow();
        }
    }
}

#[inline(never)]
fn effect_slow() {
    let now = Instant::now();
    let due = sleeper_due(now) || crate::net::due(now);
    if due {
        yield_now();
    }
}

/// Mark the event loop's context (`net`) able to run: it has events to
/// deliver.
pub fn wake_evloop() {
    let s = sched();
    if let Some(e) = s.evloop {
        if s.ctxs[e as usize].wait == Wait::Io {
            wake(e);
        }
    }
}

/// Start the event loop's context, once (`net` calls this when it starts
/// watching something).
pub fn ensure_evloop() {
    let s = sched();
    if s.evloop.is_some() {
        return;
    }
    let id = new_ctx(Kind::EvLoop, evloop_entry);
    // It starts blocked: it runs when there are events.
    let s = sched();
    let x = &mut s.ctxs[id as usize];
    x.status = Status::Blocked;
    x.wait = Wait::Io;
    s.blocked += 1;
    s.evloop = Some(id);
    // The fresh context is not in the runnable queue (`new_ctx` put it there).
    s.runnable.retain(|&c| c != id);
}

extern "C" fn evloop_entry(_: usize) -> ! {
    loop {
        crate::net::deliver();
        block(Wait::Io);
    }
}

extern "C" {
    /// lean2rr's `l2r_task_run_one() -> u64`: runs the next queued task
    /// (`task::next_tag`), exported by every program.
    #[linkage = "extern_weak"]
    static l2r_task_run_one_c: *const std::ffi::c_void;
}

extern "C" fn worker_entry(_: usize) -> ! {
    let f = unsafe { l2r_task_run_one_c };
    assert!(!f.is_null(), "leanrt: no l2r_task_run_one_c");
    let f: unsafe extern "C" fn() -> u64 = unsafe { std::mem::transmute(f) };
    loop {
        unsafe { f() };
        // Natively the worker takes the next queued task; here a context
        // that can go on comes first, and this one ends.
        let s = sched();
        if !s.runnable.is_empty() {
            break;
        }
        let e = crate::task::startable(true);
        if e == crate::task::NONE {
            break;
        }
        let s = sched();
        s.ctxs[s.cur as usize].preselect = e;
    }
    die()
}

/// End the running context (a worker with nothing left to do).
fn die() -> ! {
    let s = sched();
    let c = s.cur;
    {
        let x = &mut s.ctxs[c as usize];
        x.status = Status::Dead;
        x.wait = Wait::None;
    }
    s.workers -= 1;
    wake_progress();
    schedule();
    unreachable!("leanrt: a dead context was resumed")
}

/// A new context running `entry`, able to run.
fn new_ctx(kind: Kind, entry: extern "C" fn(usize) -> !) -> CtxId {
    let s = sched();
    let stack = match s.pool.pop() {
        Some(st) => st,
        None => match Stack::new(crate::rt::thread_stack_size()) {
            Some(st) => st,
            None => crate::rt::thread_create_failed(),
        },
    };
    let sp = stack.init(entry, 0);
    let tb = s.next_thread << 16;
    s.next_thread += 1;
    let mut x = Ctx::new(kind, tb);
    x.sp = sp;
    x.stack = Some(stack);
    let id = match s.free.pop() {
        Some(i) => {
            s.ctxs[i as usize] = x;
            i
        }
        None => {
            s.ctxs.push(x);
            (s.ctxs.len() - 1) as CtxId
        }
    };
    if kind == Kind::Worker {
        s.workers += 1;
    }
    s.runnable.push_back(id);
    id
}

/// Whether worker contexts are alive (tasks started by the scheduler that
/// have not finished).
pub fn workers_alive() -> bool {
    sched().workers > 0
}

/// Pick the next context to run and switch to it; returns when the running
/// context runs again (it has blocked, yielded or died before).
fn schedule() {
    loop {
        let s = sched();
        let next_deadline = promote_sleepers(Instant::now());
        let s2 = sched();
        if let Some(n) = s2.runnable.pop_front() {
            if s2.ctxs[n as usize].status != Status::Runnable {
                continue;
            }
            if n == s2.cur {
                s2.ctxs[n as usize].status = Status::Running;
                return;
            }
            switch_to(n);
            return;
        }
        let _ = s;
        // A queued task on a new worker context.
        let e = crate::task::startable(false);
        if e != crate::task::NONE {
            let id = new_ctx(Kind::Worker, worker_entry);
            let s = sched();
            s.ctxs[id as usize].preselect = e;
            continue;
        }
        // The event loop's timers and sockets, or the earliest sleeper.
        let timeout = next_deadline.map(|d| d.saturating_duration_since(Instant::now()));
        if crate::net::wait(timeout) {
            continue;
        }
        if let Some(t) = timeout {
            std::thread::sleep(t);
            continue;
        }
        // Nothing can go on: a program polling for a task learns that it
        // has not finished.
        if wake_pollers() {
            continue;
        }
        crate::task::hang_thread();
    }
}

/// Wake the contexts polling for a task (`Wait::CellPoll`).
fn wake_pollers() -> bool {
    let s = sched();
    let mut any = false;
    for i in 0..s.ctxs.len() {
        if matches!(s.ctxs[i].wait, Wait::CellPoll(_)) && s.ctxs[i].status == Status::Blocked {
            wake(i as CtxId);
            any = true;
        }
    }
    any
}

/// Switch from the running context to `n` (able to run).
fn switch_to(n: CtxId) {
    let s = sched();
    let c = s.cur;
    // The leaving context's bookkeeping is set aside, the arriving one's
    // put in place.
    crate::task::swap_ctx_state(&mut s.ctxs[c as usize].tasks);
    crate::once::swap_ctx_state(&mut s.ctxs[c as usize].once);
    crate::task::swap_ctx_state(&mut s.ctxs[n as usize].tasks);
    crate::once::swap_ctx_state(&mut s.ctxs[n as usize].once);
    s.ctxs[n as usize].status = Status::Running;
    s.cur = n;
    let to = s.ctxs[n as usize].sp;
    let save: *mut usize = &mut s.ctxs[c as usize].sp;
    // A dead context's stack is freed once another runs.
    if s.ctxs[c as usize].status == Status::Dead {
        let st = s.ctxs[c as usize].stack.take();
        free_zombie();
        let s = sched();
        s.zombie = st;
        s.free.push(c);
    }
    unsafe { crate::coro::switch(save, to) };
    free_zombie();
}

/// Free the stack of the context that ended last (keeping a few for reuse).
fn free_zombie() {
    let s = sched();
    if let Some(st) = s.zombie.take() {
        if s.pool.len() < 8 {
            st.release_memory();
            s.pool.push(st);
        }
    }
}
