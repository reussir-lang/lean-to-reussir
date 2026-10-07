//! lean2rr's tasks and promises over lean-runtime's task scheduler
//! (`lean_runtime::sched`): the representation glue of lean-runtime's
//! docs/sched.md, "The glue", items 3 and 4.
//!
//! The rules (when a task runs, its queues and priorities, dependents and
//! their walks, waits, polling, cancellation, the pure-task rule, promises,
//! the final run when `main` returns) are lean-runtime's. What is lean2rr's
//! is the task object and its value: a task is a runtime cell (`LCell`,
//! `drop::Cell`) whose state lean2rr generates per value type (`pending(f)`,
//! `busy`, `done(v)`, `conv(...)`, `bind(g)`; translation plan §5.14), with
//! functions that force it (`l2r_task_get_S`, ...). This module connects
//! the two through the primitives that generated code calls (`l2r_task_*`,
//! unchanged from leanrt's own scheduler), so the generated code is the
//! same:
//!
//! - **A task's id.** A cell that is a task lean-runtime has not finished
//!   has an entry here, which holds its `TaskId`; the entry's index is kept
//!   in the cell's padding (the 4 bytes after its count; `l2r_lcell_new`
//!   sets them to `NONE`). The slot comes first (lean-runtime's rule): once
//!   the cell holds `done(v)` the task has finished for lean2rr, and the id
//!   is never passed again (`TaskId::FINISHED` instead).
//! - **A task's job** (`make_job`) holds the cell's address, uncounted, and
//!   its state type's tag. Run, it gives the generated code a counted
//!   reference to the cell through the program's dispatcher
//!   (`l2r_task_run_one_c`, which asks `next_tag` and `handed`), which runs
//!   the task as a worker would (`l2r_task_step_S`): stores `done(v)`, or,
//!   for a bind task whose function returned an unfinished task, sets its
//!   continuation and reports it (`bind_wait`: `Outcome::Continue`).
//! - **The last reference.** The job holds no count, so the program's last
//!   reference to an unfinished task is the cell's last: its drop
//!   (`drop::Cell`, out of line) calls `on_last_reference`, which calls
//!   lean-runtime's `release(id)` (Lean's `deactivate_task`), IO tasks
//!   included. A pure task that has not started is deleted (its job is
//!   dropped, the cell freed); a task lean-runtime still runs keeps its cell
//!   alive: the glue takes the last reference over (`OWNED`) and gives it to
//!   the job when it runs, or drops it if lean-runtime drops the job.
//! - **Waits** (`Task.get`, `IO.wait` of a task whose cell is not `done`)
//!   are lean-runtime's `wait(id)`; the generated code then reads the
//!   value. `IO.waitAny`'s generated loop is mapped onto lean-runtime's
//!   `wait_any` (`wait_status`, `wait_progress`).
//! - **Promises** hold the cell of their task; lean-runtime's promise id is
//!   that task's. A promise dropped inside a free (whose walk runs Lean
//!   code, which may block) is resolved, its cell's store included, once
//!   the free is over (lean-runtime's deferred resolutions, core 3.3:
//!   `defer`, then `run_deferred` at the drain's end, which Reussir reports
//!   through its patch 0040).

use lean_runtime::sched::{self as ls, Deferred, Job, Outcome, TaskId, TaskState};
use std::cell::UnsafeCell;

struct Global<T>(UnsafeCell<T>);
unsafe impl<T> Sync for Global<T> {}

/// No entry.
pub const NONE: u32 = u32::MAX;

/// `kind` bits of `register`: a pure task (`keep_alive = false`), and a
/// dependent (`depend` follows and decides where it goes).
pub const K_PURE: u64 = 1;
pub const K_DEP: u64 = 2;

/// `begin` result bits: run with a stream context of its own (a worker
/// thread), and release a reference (never set: the generated code owns
/// exactly the reference it was handed).
pub const B_ENTER: u64 = 1;
pub const B_RELEASE: u64 = 2;

// Entry flags.
/// Registered as a dependent: `depend` has not been called yet.
const DEP: u16 = 1 << 0;
/// The cell holds its value: finished for lean2rr; lean-runtime's job has
/// not returned yet.
const DONE: u16 = 1 << 1;
/// `ls::release` was called (the program's last reference went).
const RELEASED: u16 = 1 << 2;
/// The glue holds the cell's last reference (the program dropped its own,
/// and lean-runtime still runs the task).
const OWNED: u16 = 1 << 3;
/// An unresolved promise's task.
const PROMISE: u16 = 1 << 4;
/// `Task.spawn`/`map`/`bind`: `keep_alive = false`.
const PURE: u16 = 1 << 5;
/// `id` is set.
const HAS_ID: u16 = 1 << 6;
/// `cont` is set (`bind_wait`).
const CONT: u16 = 1 << 7;
/// A dedicated task running with a fresh stream context (`begin`): `end`
/// ends it inside the context (`end_running_task`).
const FRESH: u16 = 1 << 8;

struct Entry {
    /// The cell's address; 0 for a free entry.
    cell: usize,
    id: TaskId,
    /// Which generated state type the cell has (lean2rr's tag).
    tag: u32,
    /// The entry's allocation number: a job names its entry by index and
    /// serial, since entries and cell addresses are reused.
    serial: u32,
    flags: u16,
    /// A dependent's `Task.Priority` until `depend` passes it to
    /// lean-runtime: the value, or `u32::MAX` for one of 2^32 or more (every
    /// priority above 8 is a dedicated task, so lean-runtime treats it as the
    /// whole value; the entry stays 40 bytes).
    prio: u32,
    /// With `CONT`: a bind task whose function returned the unfinished task
    /// `cont`: it waits for it (`bind_wait`).
    cont: TaskId,
}

/// `IO.waitAny`'s generated loop asks `wait_status` once per listed task,
/// in two passes over the list, then `wait_progress` (see `wait_status`).
enum WaitAny {
    Idle,
    /// The tasks asked about so far (both passes).
    Collect(Vec<TaskId>),
    /// lean-runtime answered: the `k`-th task of the list; `pos` tasks of
    /// the next pass asked about so far.
    Answer { k: usize, pos: usize },
}

struct Tasks {
    slab: Vec<Entry>,
    free: Vec<u32>,
    serial: u32,
    /// Entries in use.
    live: u32,
    /// The cell handed to the program's dispatcher (`handed`), with its tag
    /// (`next_tag`), to run it or, `deleting`, to drop its reference.
    handed: usize,
    handed_tag: u64,
    deleting: bool,
    /// The cell a job is running, until it begins (`begin`): its forcing
    /// code asks for its own sources (`source_next`) before it runs.
    run_cell: usize,
    wait_any: WaitAny,
}

static TASKS: Global<Tasks> = Global(UnsafeCell::new(Tasks {
    slab: Vec::new(),
    free: Vec::new(),
    serial: 0,
    live: 0,
    handed: 0,
    handed_tag: u64::MAX,
    deleting: false,
    run_cell: 0,
    wait_any: WaitAny::Idle,
}));

/// The glue's state. lean2rr runs on one thread at a time (the module
/// initializers, then `main`'s thread), and no reference is held across a
/// call that may run Lean code or the scheduler.
#[inline]
fn tasks() -> &'static mut Tasks {
    unsafe { &mut *TASKS.0.get() }
}

/// The index slot in a cell (the box's padding, after the 4-byte count).
#[inline]
fn slot(cell: usize) -> *mut u32 {
    (cell + 4) as *mut u32
}

/// Initialize a new cell's index slot (`l2r_lcell_new`).
#[inline]
pub fn init_cell(cell: usize) {
    unsafe { *slot(cell) = NONE }
}

/// The entry of the task at `cell` (a task's address for the runtime: a
/// converted copy's is its original's), if it has one.
#[inline]
fn find(cell: usize) -> Option<u32> {
    let t = tasks();
    let i = unsafe { *slot(cell) };
    if (i as usize) < t.slab.len() && t.slab[i as usize].cell == cell {
        Some(i)
    } else {
        None
    }
}

#[inline]
fn ent(i: u32) -> &'static mut Entry {
    &mut tasks().slab[i as usize]
}

/// Entry `i` if it is still the one with `serial`.
// One per unfinished task, beside lean-runtime's own entry and boxed job.
const _: () = assert!(std::mem::size_of::<Entry>() <= 40);

fn entry_at(i: u32, serial: u32) -> Option<&'static mut Entry> {
    let e = tasks().slab.get_mut(i as usize)?;
    (e.cell != 0 && e.serial == serial).then_some(e)
}

fn alloc(cell: usize, tag: u32, flags: u16, prio: u32) -> u32 {
    let t = tasks();
    t.serial = t.serial.wrapping_add(1);
    t.live += 1;
    let e = Entry { cell, id: TaskId::FINISHED, tag, serial: t.serial, flags, prio, cont: TaskId::FINISHED };
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

fn free_entry(i: u32) {
    let t = tasks();
    let e = &mut t.slab[i as usize];
    if e.cell == 0 {
        return;
    }
    e.cell = 0;
    e.flags = 0;
    t.live -= 1;
    t.free.push(i);
}

/// The id to give lean-runtime for the task at address `a`: its `TaskId`
/// while its cell does not hold its value, else `TaskId::FINISHED`.
fn id_of(a: usize) -> TaskId {
    match find(a) {
        Some(i) if ent(i).flags & (HAS_ID | DONE) == HAS_ID => ent(i).id,
        _ => TaskId::FINISHED,
    }
}

/// Add one to the cell's count (Reussir's `Rc`: a `u32` at offset 0).
fn inc(cell: usize) {
    let c = cell as *mut u32;
    unsafe { *c = (*c).checked_add(1).expect("leanrt: task cell count overflow") };
}

extern "C" {
    /// lean2rr's `l2r_task_run_one() -> u64`, exported by every program as
    /// the trampoline `l2r_task_run_one_c`: it asks `next_tag` for the tag of
    /// the cell handed over, takes it (`handed`, the reference passing to the
    /// generated code) and runs it as a worker would (`l2r_task_step_S`), or,
    /// when `deleting`, drops it.
    #[linkage = "extern_weak"]
    static l2r_task_run_one_c: *const std::ffi::c_void;
}

/// Hand `cell` (one counted reference, which passes to the generated code)
/// to the program's dispatcher, to run it, or (`delete`) to drop it.
fn dispatch(cell: usize, tag: u32, delete: bool) {
    let f = unsafe { l2r_task_run_one_c };
    assert!(!f.is_null(), "leanrt: a task without l2r_task_run_one_c");
    let f: unsafe extern "C" fn() -> u64 = unsafe { std::mem::transmute(f) };
    let t = tasks();
    t.handed = cell;
    t.handed_tag = tag as u64;
    t.deleting = delete;
    unsafe { f() };
    let t = tasks();
    t.deleting = false;
    t.handed_tag = u64::MAX;
}

/// A task's job (lean-runtime's `Job`): its entry, its cell (uncounted) and
/// tag. Dropped without running (lean-runtime deleted the task), its entry
/// goes, and the glue's reference with it (`unrun`).
struct JobRun {
    slot: u32,
    serial: u32,
    armed: bool,
}

impl Drop for JobRun {
    fn drop(&mut self) {
        if self.armed {
            unrun(self.slot, self.serial);
        }
    }
}

fn make_job(slot: u32) -> Job {
    let jr = JobRun { slot, serial: ent(slot).serial, armed: true };
    Box::new(move || {
        // The whole guard moves into the closure (a use of `jr` itself: a
        // closure using only its `Copy` fields would capture copies of them,
        // and the guard would be dropped, armed, right away).
        let mut jr = jr;
        jr.armed = false;
        run_job(jr.slot, jr.serial)
    })
}

/// Run a task's job: the generated code runs the task (`l2r_task_step_S`),
/// with a reference of its own (the glue's, if it holds the last one).
fn run_job(slot: u32, serial: u32) -> Outcome {
    let Some(e) = entry_at(slot, serial) else {
        // Not ours any more (cannot happen: an entry outlives its job).
        return Outcome::Done;
    };
    let (cell, tag) = (e.cell, e.tag);
    if e.flags & OWNED != 0 {
        e.flags &= !OWNED;
    } else {
        inc(cell);
    }
    tasks().run_cell = cell;
    dispatch(cell, tag, false);
    let t = tasks();
    if t.run_cell == cell {
        t.run_cell = 0;
    }
    let Some(e) = entry_at(slot, serial) else { return Outcome::Done };
    if e.flags & CONT != 0 {
        e.flags &= !CONT;
        let t2 = e.cont;
        // A bind task waits for the task its function returned, then runs
        // again (its state is `pending` with a continuation reading that
        // task's value).
        return Outcome::Continue(t2, make_job(slot));
    }
    free_entry(slot);
    Outcome::Done
}

/// A job lean-runtime dropped without running it (a deleted task): the
/// entry goes; a reference the glue held is dropped by the generated code.
fn unrun(slot: u32, serial: u32) {
    let Some(e) = entry_at(slot, serial) else { return };
    let (owned, cell, tag) = (e.flags & OWNED != 0, e.cell, e.tag);
    free_entry(slot);
    if owned {
        dispatch(cell, tag, true);
    }
}

/// The last reference to cell `p` is being dropped (`drop::Cell`'s drop,
/// out of line). For an unfinished task, lean-runtime's `release(id)`
/// (Lean's `deactivate_task`), once: a pure task that has not started is
/// deleted (its job dropped); a task lean-runtime still runs keeps its cell:
/// the glue takes this last reference over (true), and the job gets it
/// (also when the reference dropped is one the glue gave the job: a bind
/// task's, once its function has run). A task that has stored its value
/// (its job about to return) is released too, so that its finish notifies
/// nobody, and freed. Otherwise (false) the cell is freed as usual.
#[inline(never)]
pub fn on_last_reference(p: usize) -> bool {
    let Some(i) = find(p) else { return false };
    let e = ent(i);
    if e.flags & (PROMISE | DEP) != 0 {
        // A promise's task outlives its promise's resolution only as a
        // finished task (its entry goes then); a dependent is given to
        // lean-runtime before the generated code can drop it.
        return false;
    }
    if e.flags & (RELEASED | HAS_ID) == HAS_ID {
        e.flags |= RELEASED;
        let (id, serial) = (e.id, e.serial);
        ls::release(id);
        if entry_at(i, serial).is_none() {
            // Deleted (its job dropped, `unrun`).
            return false;
        }
    }
    let e = ent(i);
    if e.flags & DONE != 0 {
        return false;
    }
    e.flags |= OWNED;
    true
}

// ---------------------------------------------------------------------------
// The generated code's primitives

/// Whether new tasks are deferred (otherwise they run at once):
/// lean-runtime's `deferring`, true from `main`'s start (`start`) when the
/// task manager has workers (not with `LEAN_NUM_THREADS=0`), also before
/// the lazy start has built the scheduler.
#[inline]
pub fn deferring() -> bool {
    ls::deferring()
}

/// Whether every task has finished: no task has an entry (an unfinished
/// one, a promise included, always has one) and no promise a free dropped
/// waits for its resolution (lean-runtime's `deferred_pending`, which also
/// counts one a resolution under way has not reached). Then a constant's
/// walk for tasks (`persist`) can be skipped.
#[inline(never)]
pub fn settled() -> bool {
    tasks().live == 0 && !ls::deferred_pending()
}

/// The task manager (Lean's `lean_init_task_manager`): the entry point
/// calls this at `main`'s start, on `main`'s thread (the generated
/// `l2r_main_body`, inside the body `rt::run_main2` gives
/// `io::startup::run_main`: the scheduler's state is that thread's own).
/// lean-runtime's lazy start (`start_lazy`) takes the number of workers
/// (`LEAN_NUM_THREADS`, else the online processors: the same system calls as
/// natively) and the contexts' stack size (`LEAN_STACK_SIZE_KB`, else 1 GiB)
/// now, and builds the scheduler itself with lean2rr's glue at the first
/// task, promise, `Std.Sync` object or operation, timer, signal watcher or
/// socket: lean-runtime's entry points for those start it themselves
/// (`ensure_started`), and the start turns `ST.Ref` reads into polling
/// points (`set_ref_read_yields`; see `refs`). So a program that makes none
/// builds no scheduler state, context or event loop, nor pages in their
/// code. During the module initializers nothing is started: Lean has no task
/// manager then.
pub fn start() {
    ls::start_lazy(
        std::rc::Rc::new(crate::sched::LeanrtGlue),
        ls::lean_num_threads(),
        ls::thread_stack_size(),
    );
}

/// `main` has returned: lean-runtime's final run (`finish`: the remaining
/// tasks run as during Lean's task-manager shutdown, then the io layer's
/// dedicated tasks are waited for); the program's dispatcher then finds
/// nothing more to run (`next_tag`). If the scheduler was never built, the
/// same without the run of tasks: the handed-off streams' writers, then the
/// io layer's dedicated tasks (and nothing is built).
pub fn shutdown() {
    ls::finish();
}

/// `IO.sleep` / `dbgSleep`.
#[inline(never)]
pub fn sleep_ms(ms: u32) {
    ls::sleep_ms(ms)
}

/// A new deferred task at priority `prio` (Lean's `Task.Priority`, the
/// whole value; a big `Nat` is `u64::MAX`): `Task.spawn`/`IO.asTask`
/// (lean-runtime's `spawn`), or a dependent (`K_DEP`: `depend` follows).
/// Every priority above 8 is a dedicated task (lean-runtime's LB-39).
/// Returns 0 (the generated code's "run it now" answer, 1, is
/// lean-runtime's now).
#[inline(never)]
pub fn register(cell: usize, tag: u64, prio: u64, kind: u64) -> u64 {
    let mut flags = 0;
    if kind & K_PURE != 0 {
        flags |= PURE;
    }
    if kind & K_DEP != 0 {
        flags |= DEP;
    }
    let i = alloc(cell, tag as u32, flags, u32::try_from(prio).unwrap_or(u32::MAX));
    if kind & K_DEP != 0 {
        return 0;
    }
    let serial = ent(i).serial;
    let id = ls::spawn(make_job(i), prio, kind & K_PURE == 0);
    set_id(i, serial, id);
    0
}

/// The task of entry `i` (if still there and unfinished) has id `id`.
fn set_id(i: u32, serial: u32, id: TaskId) {
    if let Some(e) = entry_at(i, serial) {
        if e.flags & DONE == 0 {
            e.id = id;
            e.flags |= HAS_ID;
        }
    }
}

/// `dep` (just registered with `K_DEP`) was created depending on `src`
/// (`sync`: with `sync := true`): lean-runtime's `depend` (Lean's
/// `add_dep`). The generated code applies the function itself when `sync`
/// and `src` has finished (`dependent_runs_now`). Returns 0.
#[inline(never)]
pub fn depend(src: usize, dep: usize, sync: bool) -> u64 {
    let Some(d) = find(dep) else { return 0 };
    let e = ent(d);
    if e.flags & DEP == 0 {
        return 0;
    }
    e.flags &= !DEP;
    let (prio, keep_alive, serial) = (e.prio, e.flags & PURE == 0, e.serial);
    let src = id_of(src);
    let id = ls::depend(src, make_job(d), u64::from(prio), sync, keep_alive);
    set_id(d, serial, id);
    0
}

/// The running `bind` task `cell` has run its function, which returned the
/// unfinished task `src`: its job reports it (`Outcome::Continue`): it waits
/// for `src`, keeping its priority and flags, then runs its continuation
/// (`task_bind_fn1`).
#[inline(never)]
pub fn bind_wait(cell: usize, src: usize) {
    let id = id_of(src);
    if let Some(i) = find(cell) {
        let e = ent(i);
        e.cont = id;
        e.flags |= CONT;
    }
}

/// A task starts running (the generated `l2r_task_begin`, inside its job):
/// `B_ENTER` for a dedicated task, which natively runs on a thread of its
/// own with the process's streams, so with a fresh stream context
/// (`sched::fresh_context`); a pool task has its worker's cells already
/// (`Glue::task_begin`), a `sync` task shares its thread's.
#[inline(never)]
pub fn begin(cell: usize) -> u64 {
    let t = tasks();
    if t.run_cell == cell {
        t.run_cell = 0;
    }
    if crate::sched::fresh_context() {
        if let Some(i) = find(cell) {
            ent(i).flags |= FRESH;
        }
        B_ENTER
    } else {
        0
    }
}

/// The running task `cell` has stored its value: it has finished for
/// lean2rr (its id is no longer given out). A dedicated task ends here, in
/// lean-runtime too (`end_running_task`, with the id `spawn` or `depend`
/// gave it): its `sync` dependents run now, inside its stream context,
/// which the generated code closes next (natively they run on its thread
/// with the streams it left). Otherwise lean-runtime ends the task once the
/// job returns: a pool task's worker cells and a `sync` task's thread stay
/// installed until then. A job that runs before `spawn` or `depend` has
/// returned has no id yet: it ends when it returns, on the thread that ran
/// it. In lean2rr's single-thread build that is only a job of `spawn`
/// without a task manager (during the module initializers, or with
/// `LEAN_NUM_THREADS=0`), which runs inside the call; in lean-runtime's
/// threads mode a worker thread can also start a job before `spawn` or
/// `depend` returns. Returns 0.
#[inline(never)]
pub fn end(cell: usize) -> u64 {
    if let Some(i) = find(cell) {
        let e = ent(i);
        let fresh = e.flags & (FRESH | CONT) == FRESH;
        let id = if e.flags & HAS_ID != 0 { e.id } else { TaskId::FINISHED };
        e.flags |= DONE;
        if fresh {
            ls::end_running_task(id);
        }
    }
    0
}

/// The generated code's wait for task `a` (`Task.get`, `IO.wait`), whose
/// cell does not hold its value yet: lean-runtime's `await_task` (in a
/// `sync := true` task, the Lean panic native `Task.get` prints,
/// `GET_IN_SYNC_TASK`, then `wait(id)`). Nothing for the task a job is
/// about to run (its forcing code first asks for its own sources).
fn await_task(a: usize) {
    // First: between a job's hand-over and its `begin` nothing else may run
    // (a nested job would take `run_cell`).
    if tasks().run_cell == a {
        return;
    }
    ls::await_task(id_of(a), |msg| crate::lean_panic(msg.as_bytes(), false));
}

/// Before pending task `a` runs (`l2r_task_force_sources`): it is waited
/// for (lean-runtime runs it, or what it waits for, once a worker would);
/// then nothing is left for the generated code to run (`u64::MAX`).
#[inline(never)]
pub fn source_next(a: usize) -> u64 {
    await_task(a);
    u64::MAX
}

/// `Task.get` of a `busy` task `a` (running on another context, or on this
/// one: it needs itself, and waits forever, as natively).
#[inline(never)]
pub fn wait_running(a: usize) -> u64 {
    await_task(a);
    1
}

/// The task handed over (`dispatch`), with its reference.
#[inline(never)]
pub fn handed() -> usize {
    let t = tasks();
    let c = t.handed;
    assert!(c != 0, "leanrt: no task handed over");
    t.handed = 0;
    c
}

/// Whether the cell handed over is to be dropped rather than run.
#[inline]
pub fn deleting() -> bool {
    tasks().deleting
}

/// The tag of the cell handed over (`dispatch`), once; `u64::MAX` when none
/// is (the generated final run, `l2r_run_pending_tasks`, after
/// lean-runtime's `finish`, finds none).
#[inline(never)]
pub fn next_tag() -> u64 {
    std::mem::replace(&mut tasks().handed_tag, u64::MAX)
}

/// The generated walk of a finished task's dependents (`l2r_task_walk`):
/// lean-runtime walks them; nothing is ever handed here.
#[inline]
pub fn walk_next() -> u64 {
    u64::MAX
}

/// Whether task `a` has finished for lean2rr: 2; otherwise 1 (only "has
/// finished" is read: `Task.map` with `sync := true`, a bind step).
#[inline(never)]
pub fn status(a: usize) -> u8 {
    if id_of(a) == TaskId::FINISHED {
        2
    } else {
        1
    }
}

/// `IO.getTaskState` (lean-runtime's `state`, a polling point): 0 waiting,
/// 1 running, 2 finished.
#[inline(never)]
pub fn query(a: usize) -> u8 {
    let id = id_of(a);
    if id == TaskId::FINISHED {
        return 2;
    }
    match ls::state(id) {
        TaskState::Waiting => 0,
        TaskState::Running => 1,
        TaskState::Finished => 2,
    }
}

/// `IO.waitAny`: the generated loop asks this for each task of the list in
/// order (a first pass, which takes a task answered 2, finished; a second,
/// which runs a task answered 0, waiting), then `wait_progress` (waits, then
/// starts over). The list is collected over both passes (answered 1, so
/// neither takes anything); `wait_progress` hands it to lean-runtime's
/// `wait_any`, and the next first pass is answered 2 at the position
/// lean-runtime chose. Positions, not addresses, are counted, so a list
/// with a task twice works. No context switch happens between the calls of
/// a pass (they only read the list); the state is set aside during
/// lean-runtime's wait, where other contexts run their own `IO.waitAny`.
#[inline(never)]
pub fn wait_status(a: usize) -> u8 {
    let t = tasks();
    match &mut t.wait_any {
        WaitAny::Idle => {
            t.wait_any = WaitAny::Collect(vec![id_of(a)]);
            1
        }
        WaitAny::Collect(ids) => {
            ids.push(id_of(a));
            1
        }
        WaitAny::Answer { k, pos } => {
            if *pos == *k {
                t.wait_any = WaitAny::Idle;
                2
            } else {
                *pos += 1;
                1
            }
        }
    }
}

/// `IO.waitAny` after both passes (`wait_status`): lean-runtime's
/// `wait_any` over the list, then 1 (the generated loop starts over and
/// takes the task it chose). 0 (wait forever) for an empty list, which Lean
/// rules out (`IO.waitAny` takes a proof that the list is not empty).
#[inline(never)]
pub fn wait_progress() -> u64 {
    let t = tasks();
    let WaitAny::Collect(ids) = std::mem::replace(&mut t.wait_any, WaitAny::Idle) else {
        return 0;
    };
    let n = ids.len() / 2;
    debug_assert!(ids.len() == 2 * n && ids[..n] == ids[n..], "leanrt: IO.waitAny's passes differ");
    if n == 0 {
        return 0;
    }
    let k = ls::wait_any(&ids[..n]);
    tasks().wait_any = WaitAny::Answer { k, pos: 0 };
    1
}

/// `IO.cancel` of task `a`.
#[inline(never)]
pub fn cancel(a: usize) {
    let id = id_of(a);
    if id != TaskId::FINISHED {
        ls::cancel(id);
    }
}

/// `IO.checkCanceled` (lean-runtime's, a polling point).
#[inline(never)]
pub fn check_canceled() -> bool {
    ls::check_canceled()
}

/// The running context waits forever (lean-runtime's `hang`).
pub fn hang() -> ! {
    ls::hang()
}

// ---------------------------------------------------------------------------
// Promises

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
        if crate::drop::active() {
            // Released while a container is freed: the free reaches it in
            // Lean's order (`crate::drop`), and there releases a resolved
            // promise's cell or puts an unresolved one's resolution off.
            crate::drop::defer(self.cell, defer_promise_drop);
            return;
        }
        unsafe { drop_promise_now(self.cell) };
    }
}

/// The free reaches a promise it released (a step of Reussir's drain, in
/// Lean's order).
/// - Resolved: there is nothing to resolve, and the promise's reference to
///   its cell goes right there, so what the cell holds is released in the
///   free's order, as natively (plan §10, "Order of releases in one free";
///   review RS6-01, test `RtPromiseResolvedFreeOrder`). Its status cannot
///   change between the promise's drop and this step: no Lean code runs in
///   a free.
/// - Unresolved: natively its resolution with `none` runs right there, its
///   `sync` dependents included (`deactivate_promise`), but they are Lean
///   code that may block, and no context may suspend inside a free (the
///   free is the thread's, `reussir_rt::drop`; lean-runtime's no-suspend
///   scope, its rules R1-R3). So the whole resolution, the cell's store
///   included, is put off until the drain is over (lean-runtime's `defer`,
///   core 3.3), and runs there in the order the free reached the promises
///   (`drained`). With the store made there too, the other contexts see
///   the promise unresolved until its dependents run, as natively (the
///   store-with-resolve shape of the design's review RW1-05).
unsafe fn defer_promise_drop(cell: usize) -> bool {
    if promise_resolved(cell) {
        return drop_promise_now(cell);
    }
    hook_drained();
    ls::defer(Deferred::Call(Box::new(move || unsafe {
        drop_promise_now(cell);
    })));
    true
}

/// The generated `l2r_promise_drop` resolves the promise with `none` unless
/// it is resolved already (its cell's store, a publication, then
/// lean-runtime's `resolve`, which walks its dependents), and releases the
/// promise's reference to its cell. Inside a free only for a resolved
/// promise, where it is that release alone (`defer_promise_drop`).
unsafe fn drop_promise_now(cell: usize) -> bool {
    let f = l2r_promise_drop_c;
    assert!(!f.is_null(), "leanrt: promise without l2r_promise_drop_c");
    let f: unsafe extern "C" fn(usize) -> u64 = std::mem::transmute(f);
    f(cell);
    true
}

pub type LPromise = reussir_rt::rc::Rc<Box<dyn std::any::Any>>;

/// `IO.Promise.new`: a promise for the new unresolved task `cell` (whose
/// reference it takes), lean-runtime's `promise_new`. Before the task
/// manager runs, Lean's internal panic.
#[inline(never)]
pub fn promise_new(cell: usize) -> LPromise {
    match ls::promise_new() {
        Ok(id) => {
            let i = alloc(cell, 0, PROMISE | HAS_ID, 0);
            ent(i).id = id;
        }
        Err(msg) => crate::internal_panic(msg),
    }
    reussir_rt::rc::Rc::new(Box::new(Promise { cell }) as Box<dyn std::any::Any>)
}

/// The cell of promise `p`'s task (borrowed).
#[inline(never)]
pub fn promise_cell(p: &LPromise) -> usize {
    p.downcast_ref::<Promise>().expect("leanrt: not a promise").cell
}

/// Promise `a` was resolved (the generated `l2r_promise_resolve_S` has
/// stored `done(v)` in its cell, `v` being `some x` or, for a dropped
/// promise, `none`): lean-runtime's `resolve`, which walks its dependents
/// here. Never inside a free: a promise a free drops is resolved after it
/// (`defer_promise_drop`), and no Lean code runs in a free; if it ever were
/// (checked in debug builds), lean-runtime would put the walk off to the
/// drain's end. Returns 0 (lean-runtime walks the dependents).
#[inline(never)]
pub fn resolve(a: usize) -> u64 {
    let Some(i) = find(a) else { return 0 };
    let e = ent(i);
    if e.flags & PROMISE == 0 {
        return 0;
    }
    let id = e.id;
    free_entry(i);
    if crate::drop::active() {
        debug_assert!(false, "leanrt: a promise resolved inside a free");
        hook_drained();
        ls::defer(Deferred::Resolve(id));
        return 0;
    }
    ls::resolve(id, || {});
    0
}

/// Have Reussir's drains call `drained` when they end: the function every
/// drain that released something calls once it is over
/// (`reussir_rt::drop::__reussir_drop_drained`, local Reussir patch 0040,
/// which lean2rr requires: `scripts/l2r.py` checks for it, and this
/// reference does not link without it).
fn hook_drained() {
    let f: extern "C" fn() = drained;
    reussir_rt::drop::__reussir_drop_drained.store(f as *mut (), std::sync::atomic::Ordering::Relaxed);
}

/// A drain is over (`__reussir_drop_drained`, outside it): the resolutions
/// put off inside it run, in order, on this context (lean-runtime's
/// `run_deferred`; a free inside one of them resolves its own promises at
/// its own end, before the next, as natively a free inside a dependent).
extern "C" fn drained() {
    // nothing queued: no out-of-line call (lean-runtime's count of pending
    // resolutions covers the queued ones; review RS6-04)
    if !crate::drop::active() && ls::deferred_pending() {
        ls::run_deferred();
    }
}

/// Whether the promise whose task is `cell` has been resolved (no polling
/// point): its entry goes at the resolution.
pub fn promise_resolved(cell: usize) -> bool {
    find(cell).is_none()
}

/// `IO.Promise.isResolved` (lean2rr's shim, `L2RShim.promiseIsResolved`):
/// `IO.hasFinished` of the promise's task (lean-runtime's `state`, a
/// polling point). The caller releases the promise afterwards: natively
/// `isResolved` borrows it.
#[inline(never)]
pub fn promise_is_resolved(cell: usize) -> bool {
    query(cell) == 2
}
