//! The glue between lean2rr's runtime and lean-runtime's task scheduler
//! (`lean_runtime::sched`, its features `sched` and `stack-overflow`).
//!
//! The scheduler is lean-runtime's: Lean's task manager on one thread, its
//! contexts (corosensei coroutines, every switch through `main`'s stack and
//! its hub), the order in which they run, the effect and polling points,
//! the event loop, `Std.Sync`'s locks and Lean's stack-overflow report
//! (lean-runtime's `docs/sched.md`). This module is what lean-runtime asks
//! of a translator's glue (`docs/sched.md`, "The glue"):
//!
//! - the one `unsafe` step of the switch (`Glue::suspend`, below);
//! - what a thread owns natively and a context owns here: the current
//!   standard streams of `IO.setStdout` & co. (lean2rr's mutable once-cells,
//!   `once::CtxState`), and the outcome of the last IO primitive, which
//!   the program reads after the call (`fs::LastError`), set aside and
//!   given back at each switch (`Glue::switched`); a pool task runs with the cells of its emulated
//!   worker (lean-runtime's `running_worker`), which keeps what the task
//!   leaves, as a native worker thread keeps its streams (`Glue::task_begin`,
//!   `task_end`); a dedicated task with a fresh stream context, which the
//!   generated code opens and closes (`l2r_task_begin`, `task::begin`);
//! - the waits of lean2rr's own objects, thin calls to lean-runtime's wait
//!   cores (core 3.1, keyed by the thunk's address): a thunk being forced on
//!   another context (`thunk_wait_busy`, `on_finish`);
//! - thin calls to the yield points (`effect`, `poll`, `before_publish`).
//!
//! lean2rr stays on one thread (`main`'s): `task::start` (lean-runtime's
//! `start_lazy`) runs there, and the scheduler is built there at the first
//! task, promise, `Std.Sync` object or operation, timer, signal watcher or
//! socket.

use crate::once;
use lean_runtime::sched::{self as ls, CtxId, Glue, Suspend};
use std::cell::RefCell;
use std::collections::HashMap;

/// lean2rr's glue, given to lean-runtime's scheduler by `task::start`.
pub(crate) struct LeanrtGlue;

impl Glue for LeanrtGlue {
    fn suspend(&self, s: Suspend<'_>) {
        // SAFETY: the one `unsafe` step of lean-runtime's scheduler, done by
        // the translator's glue (lean-runtime docs/sched.md, "Why
        // `Glue::suspend` is sound", S1-S7, and its checklist for glue
        // authors; the shared-runtime decision that each translator's glue
        // does this dereference with a full entry).
        //
        // What is dereferenced: `s.yielder()`, a `*const
        // corosensei::Yielder<(), ()>`. It is sound when, for the whole call,
        // (P1) it points to the `Yielder` of a live corosensei coroutine and
        // (P2) that coroutine is the one running on the current stack, and the
        // call is made from that coroutine's own stack.
        //
        // Why P1 and P2 hold: lean-runtime calls `Glue::suspend` from one
        // place only, `switch_away` (`src/sched/ctx.rs`), only when the running
        // context is not `main`'s (S3), with the pointer read from the
        // running context's own `Ctx::yielder` field in the same borrow that
        // records the context as blocked or able to run (S1: that field is
        // written only by the coroutine's own entry, with corosensei's `y`,
        // and cleared after the coroutine returns; S2: the running context is
        // the one whose stack this call runs on). corosensei keeps the yielder
        // (the coroutine's parent link) at a fixed place below the base of
        // the coroutine's stack, a mapping that lives until the coroutine is
        // dropped, which lean-runtime never does while it is suspended (S5).
        // `switch_away` asserts the pointer is not null.
        //
        // What lean2rr guarantees in return (the glue's duties, all checked
        // by inspection of leanrt):
        // - this body is the only dereference, once per call, and does
        //   nothing else; the `Suspend` and the pointer are not stored, copied
        //   out or used anywhere else (no field, thread-local or closure);
        // - lean-runtime's scheduler functions are called only from `main`'s
        //   thread stack and its contexts: never from a signal handler (the
        //   stack-overflow report is lean-runtime's own and calls no
        //   scheduler function), from another thread (leanrt's only other
        //   threads are lean-runtime's internal helpers, which run no Lean
        //   code), or from a stack lean2rr switches to itself (it has none:
        //   leanrt has no coroutines of its own);
        // - `switched` only moves state and cannot block or yield (below);
        // - `ls::start_lazy` is called on the thread that runs `main`
        //   (`task::start`, inside the body `rt::run_main2` gives
        //   `io::startup::run_main`), so the scheduler is built there, and
        //   every later call is made on that thread.
        unsafe { (*s.yielder()).suspend(()) }
    }

    /// Natively each thread has its own current standard streams: the
    /// leaving context's stream cells and saved stream contexts go to its
    /// record, the arriving context's come back from its own (empty for a
    /// context on a fresh id: its streams are rebuilt as the process's on
    /// first use; a context on the id of one that ended gets what that one
    /// left, which tasks keep empty: they run with a worker's set or a
    /// fresh stream context). So does the outcome of its last IO
    /// primitive, which its code reads after the call (`fs::LastError`,
    /// hunt HCO-01; review RHCO-01 for a reused id).
    /// Moves values only: no Lean code, no call into the scheduler.
    ///
    /// A context that has ended leaves its state here too, under its id, and
    /// a new context that reuses the id starts with it: lean-runtime's `Glue`
    /// reports no context's end (its hub knows it, `after_resume`'s `ended`),
    /// so neither a fix nor a check is possible here (review HL-01's
    /// suspicion a, latent). A task gives its context's cells back when it
    /// ends (`task_end`; a dedicated task's fresh stream context is closed
    /// by the generated code), so an ended task context leaves empty cells;
    /// only Lean code run on a context outside a task (a promise's `sync`
    /// dependents on the event loop's context) can leave streams behind.
    fn switched(&self, from: CtxId, to: CtxId) {
        CTX_STATES.with(|m| {
            let mut m = m.borrow_mut();
            let (mut st, mut last) = m.remove(&to).unwrap_or_default();
            once::swap_ctx_state(&mut st);
            crate::fs::swap_last(&mut last);
            m.insert(from, (st, last));
        });
    }

    /// A task starts. On a thread of its own natively (`own_thread`):
    /// - a pool task (lean-runtime's `running_worker` names its emulated
    ///   worker): that worker's stream cells come in, the running thread's
    ///   are kept until `task_end` (the worker's first task: empty cells,
    ///   rebuilt as the process's streams on first use);
    /// - a dedicated task (no worker): a fresh stream context, which the
    ///   generated code opens and closes (`l2r_task_begin` answers
    ///   `B_ENTER`, `task::begin`; `task::end` ends the task inside it).
    ///
    /// A `sync` task (not `own_thread`) shares the running thread's cells.
    /// Moves values only: no Lean code.
    fn task_begin(&self, own_thread: bool) {
        let run = if !own_thread {
            TaskRun::Shared
        } else {
            // After the workers ended (`workers_end`), a pool task (a
            // dedicated task's dependent, Lean's LB-13 run corrected) starts
            // with a fresh set, dropped at its end: as a dedicated task.
            match ls::running_worker().filter(|_| !WORKERS_ENDED.with(|e| e.get())) {
                Some(w) => {
                    let mut set = WORKER_SETS
                        .with(|s| s.borrow_mut().get_mut(w as usize).and_then(Option::take))
                        .unwrap_or_default();
                    once::swap_cells(&mut set);
                    TaskRun::Worker(w, set)
                }
                None => TaskRun::Fresh,
            }
        };
        let me = ls::current_context();
        RUNS.with(|r| r.borrow_mut().entry(me).or_default().push(run));
    }

    /// The task manager's finalization ends its standard workers, before it
    /// waits for the dedicated tasks (lean-runtime's AR-34; natively
    /// `~task_manager` joins them, and their thread finalizers drop their
    /// current streams): the workers' stream cells are dropped
    /// (`workers_end`). Called once.
    fn workers_end(&self) {
        WORKERS_ENDED.with(|e| e.set(true));
        workers_end();
    }

    /// The task started by the matching `task_begin` has finished (its
    /// `sync` dependents have run with its streams), or waits for the task
    /// its bind function returned: a pool task's worker keeps the cells the
    /// task leaves, and the running thread's come back.
    fn task_end(&self, _own_thread: bool) {
        let me = ls::current_context();
        let run = RUNS.with(|r| r.borrow_mut().get_mut(&me).and_then(Vec::pop));
        if let Some(TaskRun::Worker(w, mut set)) = run {
            once::swap_cells(&mut set);
            WORKER_SETS.with(|s| {
                let mut s = s.borrow_mut();
                let w = w as usize;
                if s.len() <= w {
                    s.resize_with(w + 1, || None);
                }
                s[w] = Some(set);
            });
        }
    }
}

/// How a task running on a context got its standard streams
/// (`Glue::task_begin`).
enum TaskRun {
    /// A `sync` task: the running thread's.
    Shared,
    /// A pool task of this emulated worker; the running thread's cells are
    /// kept here meanwhile.
    Worker(u32, once::CellSet),
    /// A dedicated task: a fresh context, opened by the generated code.
    Fresh,
}

thread_local! {
    /// The stream state and the last IO outcome of each suspended context
    /// (see `switched`).
    static CTX_STATES: RefCell<HashMap<CtxId, (once::CtxState, crate::fs::LastError)>> =
        RefCell::new(HashMap::new());
    /// The tasks running on each context, innermost last (`Glue::task_begin`).
    static RUNS: RefCell<HashMap<CtxId, Vec<TaskRun>>> = RefCell::new(HashMap::new());
    /// The workers have ended (`Glue::workers_end`).
    static WORKERS_ENDED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// Each emulated pool worker's stream cells between its tasks, by worker
    /// id (`Glue::task_end`).
    static WORKER_SETS: RefCell<Vec<Option<once::CellSet>>> = const { RefCell::new(Vec::new()) };
}

/// Whether the innermost task running on this context is a dedicated one,
/// which gets a fresh stream context (`Glue::task_begin`); false outside
/// tasks.
pub fn fresh_context() -> bool {
    let me = ls::current_context();
    RUNS.with(|r| matches!(r.borrow().get(&me).and_then(|v| v.last()), Some(TaskRun::Fresh)))
}

extern "C" {
    /// The generated `l2r_std_drop_workers` (programs that create tasks):
    /// each worker's cells in turn made current (`worker_streams_enter`)
    /// and dropped.
    #[linkage = "extern_weak"]
    static l2r_std_drop_workers_c: *const std::ffi::c_void;
}

/// The task manager's finalization joins the pool workers, whose thread
/// finalizers drop their current streams (lean-runtime's AR-33, AR-34;
/// `Glue::workers_end`): the workers' stream cells are dropped, through the
/// generated `l2r_std_drop_workers` (absent without tasks or standard
/// streams).
fn workers_end() {
    let f = unsafe { l2r_std_drop_workers_c };
    if f.is_null() {
        return;
    }
    let f: unsafe extern "C" fn() -> u64 = unsafe { std::mem::transmute(f) };
    unsafe { f() };
}

/// The task manager's finalization (`main` has returned and its tasks
/// have run): natively it joins the pool workers, whose thread finalizers
/// drop their current streams (lean-runtime's AR-33). The next worker's
/// cells, in worker order, become the current ones, the running thread's set
/// aside (`once::enter_cells`; the generated `l2r_std_leave` then drops
/// them and gives the thread's back). Whether there was one.
pub fn worker_streams_enter(base: u64) -> bool {
    let next = WORKER_SETS.with(|s| s.borrow_mut().iter_mut().find_map(Option::take));
    match next {
        Some(set) => {
            once::enter_cells(base, set);
            true
        }
        None => false,
    }
}

/// An observable effect (output, a flush, a process spawn,
/// `IO.Process.exit`): what native threads would have done by now goes
/// first (lean-runtime's `sched::effect`).
#[inline]
pub fn effect() {
    ls::effect()
}

/// A polling point (clock reads, lean-runtime's `sched::poll`).
#[inline]
pub fn poll() {
    ls::poll()
}

/// A write another context can see (a thunk's or a task's value stored in
/// its cell, `l2r_lcell_set`): the streams this context's drops handed to
/// writer threads are written first (lean-runtime's `sched::before_publish`;
/// one relaxed load when none is).
#[inline]
pub fn before_publish() {
    ls::before_publish()
}

/// `std::thread::hardware_concurrency()` (lean-runtime's).
pub fn hardware_concurrency() -> u32 {
    ls::hardware_concurrency()
}

/// A thunk has its value (`l2r_thunk_done`, after its store in
/// `l2r_lcell_set`, which makes the writers point): the contexts waiting
/// for it go on (lean-runtime's `done_keyed`, under the thunk's address;
/// one thread-local load when none waits).
#[inline]
pub fn on_finish(a: usize) {
    ls::done_keyed(a)
}

/// A `busy` thunk is needed (`l2r_thunk_wait_busy`): another context is
/// forcing it (its computation blocked, or let others run at an effect
/// point); wait until it has its value (`on_finish`), as natively a thread
/// waits for the one forcing it (lean-runtime's `wait_running_keyed`: the
/// generated `busy` state does not name the forcer). Needed by its own
/// computation, it waits forever, as natively (LB-08: native spins), the
/// others go on; before the task manager runs, or with no other context,
/// the thread hangs.
#[inline(never)]
pub fn thunk_wait_busy(a: usize) {
    crate::drop::assert_not_in_free("a thunk's wait");
    ls::wait_running_keyed(a)
}

/// A thunk forced from its own computation, tasks waiting for each other:
/// the running context waits forever while the others go on (lean-runtime's
/// `sched::hang`).
pub fn hang() -> ! {
    ls::hang()
}
