# The generated task primitives on lean-runtime's scheduler

Paths: `lean2rr/LeanToReussir/` for lean2rr's files, `runtime/` for the
runtime. Plan [§5.14](../../translation-plan.md#514-thunks-and-tasks)
("Tasks"). When a task runs (deferred until needed, the running code
blocking with a worker free, an effect point, polling, `main` returning),
which task a free worker takes, the pure-task rule, priorities, cancellation
and the final run are lean-runtime's rules (its `docs/sched.md`); the
entries here are how lean2rr's generated code reaches them.

### The generated code's primitives call lean-runtime

- **What:** The generated task code (creation `l2r_task_{defer,lazy,bind,
  lazybind}_S`, forcing `l2r_task_get_S`, the bind step, the dispatcher
  `l2r_task_run_one`) was written for leanrt's own scheduler; its
  primitives (`l2r_task_*` in the prelude, `leanrt::task`) map it onto
  lean-runtime's API: `register` is `spawn` (or, for a dependent, records
  the task until `depend_at`, which is `depend`); `wait` (a forcer's wait
  for a pending task, `l2r_task_source_next_at`, and for a `busy` one,
  `l2r_task_wait_running`) is `await_task` (lean-runtime's `wait`, after
  `Task.get`'s panic in a `sync` task); `query`
  is `state`; `cancel` (`l2r_task_cancel<S>`, which takes the task's cell,
  hunt HTG-02), `check_canceled`, `sleep_ms`, `shutdown` (`finish`) and
  `promise_new` are the calls of the same names; `deferring` is
  `manager_running`, read from the numbers `main`'s start read
  (lean-runtime starts at the first task:
  [scheduler.md](scheduler.md#lean-runtimes-scheduler-starts-at-the-first-task)).
  The answers that only leanrt's own scheduler gave are gone:
  `register`, `depend`, `end` and `wait` answer nothing (lean-runtime runs
  nothing inside `spawn` and runs a `sync` dependent inside `depend`
  itself, walks the dependents once the job has returned, and its `wait`
  runs what the task needs), and their prelude primitives answer 0, which
  the generated code does not read. The
  generated code has one dispatcher, `l2r_task_run_one`; the walk
  (`l2r_task_walk`, `l2r_task_walk_if`, the trampoline `l2r_task_walk_c`),
  the run of a task's sources (`l2r_task_force_sources`, now a direct call
  of `l2r_task_source_next_at`), the final run after `main`
  (`l2r_run_pending_tasks`), the "run it now" branches after `register`
  and `depend`, and the prelude's `l2r_task_walk_next` and
  `l2r_task_handed` were removed (task glue cleanup, 2026-10-27; they ran
  nothing on lean-runtime), and with them leanrt's `walk_next`. Two
  never-taken branches stay as fallbacks:
  `IO.getTaskState`'s branch for an answer other than 0, 1 or 2, which
  holds the task's cell across the query
  ([the program's last reference](#the-programs-last-reference-releases-a-task)),
  and `IO.waitAny`'s second pass, which only collects
  ([below](#iowaitanys-generated-loop-is-mapped-onto-lean-runtimes-wait_any)).
- **Why:** One runtime (switch step 4): the scheduler is lean-runtime's.
  The switch kept the generated code (the step's condition: the corpus's
  `.rr` outside the prelude was unchanged); the parts that only leanrt's
  own scheduler used went later.
- **Where:** `runtime/leanrt/src/task.rs`; `runtime/prelude.rr` (the
  `l2r_task_*` textures); `Lower/LazyGlue.lean` (`taskNewFn`,
  `taskDepend`, `taskStateFn`, `taskWaitAnyFn`), `Lower/LazyForce.lean`
  (`lazyGetFn`, `taskBindStepFn`), `Lower/Promises.lean`
  (`taskDispatchFns`).
- **Remove only if:** lean2rr generates code for lean-runtime's API
  directly (fewer calls; a change of every task program's code).

### A task's job runs it through the program's dispatcher

- **What:** lean-runtime runs a task by calling its job (`Job`). lean2rr's
  job holds its entry's index and allocation number (12 bytes; the entry
  holds the cell's address, without a count, and the state type's tag, in
  40 bytes); run, it gives the generated code one counted reference to the cell
  (the glue's own when it holds the last one, `OWNED`, else a new one),
  hands it with its tag (`handed`, `next_tag`) to the program's
  dispatcher `l2r_task_run_one_c`, which runs the task as a worker would
  (`l2r_task_step_S`): the forcing code's wait for the task
  (`wait`) returns at once for it (`run_cell`), `l2r_task_begin`
  answers whether it runs as on a worker thread (lean-runtime's
  `Glue::task_begin`), and `l2r_task_end` marks it finished for lean2rr
  (`DONE`). A bind task whose function returned an unfinished task reports
  it (`bind_wait`), and the job returns `Outcome::Continue` with a job for
  the continuation the generated code stored.
- **Why:** lean-runtime's jobs are boxed closures; lean2rr's tasks are
  run by generated code, which only the program's dispatcher can call
  (one entry point; the tag is that of the one task state type, 0, and the
  dispatcher has one arm, `taskDispatchFns`). The job and the entry are kept
  small: lean-runtime keeps its own slab entry and the boxed job for every
  unfinished task besides (its `docs/sched.md`, "Per-task cost"), about
  twice leanrt's own scheduler's bookkeeping per live task.
- **Where:** `runtime/leanrt/src/task.rs`: `make_job`, `run_job`,
  `dispatch`, `begin`, `end`, `bind_wait`, `JobRun`;
  `Lower/Promises.lean`: `taskDispatchFns`.
- **Remove only if:** never.

### The program's last reference releases a task

- **What:** A job holds no count, so the program's last reference to an
  unfinished task is its cell's last: the cell's drop (`drop::Cell`, out
  of line) calls `task::on_last_reference`, which calls lean-runtime's
  `release(id)` once (Lean's `deactivate_task`), IO tasks included. A pure
  task that has not started is deleted: lean-runtime drops its job, and the
  cell is freed as usual (dropping its state releases its source, which
  may be deleted in turn: a whole chain of dropped pure tasks goes, as
  natively). A task lean-runtime still runs (an IO task, a started pure
  one) keeps its cell: the glue takes the last reference over (`OWNED`)
  and gives it to the job; a job lean-runtime drops without running it
  (`JobRun`'s drop: a bind continuation of a deleted task) frees the entry
  and has the generated code drop that reference (`dispatch` with
  `deleting`). A task that has stored its value is released too (its
  finish notifies nobody, as natively) and freed. For every kind of task
  (pool, dedicated, `sync`) the job's reference goes inside the generated
  `l2r_task_end`, right after `task::end` marks the entry `DONE`, and
  lean-runtime ends the task only once the job has returned: so a task
  whose program reference went while it ran is released before its end,
  and its end wakes no waiter. A generated primitive that takes a task's
  address (`l2r_lcell_addr`, which releases the reference passed) is
  given a cell the code uses again on some path after the call, or that a
  closure built before it holds, so the call never frees it; `IO.cancel`
  passes the cell itself (`l2r_task_cancel<S>`: the cancel, then the
  release, which may be the last).
- **Why:** lean-runtime's glue item 3: "call `release(id)` for every
  task, IO tasks included" (a glue that skips it wakes waiters where
  native does not: cases `tasks/sync_walk_mutex_unref_finish`,
  `wait_any_unref_finish`). Lean deletes a pure task the program drops
  before a worker started it (adv4 TK4-01; leanrt's own scheduler read
  cell counts for it, `droppable_in`, which lean-runtime replaced with
  `release`). Natively an IO task holds a reference to itself while it
  runs (`keep_alive`) and drops it when its closure returns; if that is
  the last, the task is deleted (`m_deleted`) and freed without
  `resolve_core`'s `notify_all`. Hunt HTG-01 (test
  `RtDroppedDedicatedNotify`): `task::end` ended a dedicated task in
  lean-runtime inside its job (`end_running_task`), before the job's
  reference went, so lean-runtime walked with notification and woke an
  `IO.waitAny` that natively waits for the next finish. Natively
  `lean_io_cancel` borrows the task and the caller's decrement follows;
  hunt HTG-02 (test `RtTaskCancelLastUse`, which exercises the path; the
  read itself shows in no output): the generated `IO.cancel` passed
  `l2r_lcell_addr(t)`, and when `IO.cancel` was `t`'s last use and `t` had
  finished, the cancel read the index slot of the freed cell.
- **Where:** `runtime/leanrt/src/task.rs`: `on_last_reference`, `unrun`,
  `JobRun`, `end`, `cancel`; `runtime/leanrt/src/drop.rs`: `free_cell`;
  `runtime/prelude.rr`: `l2r_task_end`, `l2r_lcell_addr`,
  `l2r_task_cancel`; `Lower/LazyGlue.lean`: `IO.cancel`, `taskStateFn`.
- **Remove only if:** never.

### `IO.waitAny`'s generated loop is mapped onto lean-runtime's `wait_any`

- **What:** The generated `IO.waitAny` asks `l2r_task_wait_status_at` for
  each task of the list, in a first pass (which takes a task answered 2)
  and a second (which runs a task answered 0), then calls
  `l2r_task_wait_progress` and starts over. The glue answers 1 to both
  passes while it collects the list (both passes: twice the list), then
  `wait_progress` calls lean-runtime's `wait_any` on it and the next first
  pass is answered 2 at the position lean-runtime chose. The glue never
  answers 0, so the second pass only collects; it stays because
  `wait_progress` takes the list as its two equal halves. Positions, not
  addresses, are counted (a list may name a task twice). No context switch
  happens inside a pass; the state is set aside during lean-runtime's wait,
  where other contexts run their own `IO.waitAny`.
- **Why:** lean-runtime's `wait_any` takes the whole list and decides
  alone (its notification rule, RS2-06; what runs on the waiter's stack,
  AR-10); the generated code asks per task (see the first entry).
- **Where:** `runtime/leanrt/src/task.rs`: `wait_status`,
  `wait_progress`, `WaitAny`; `Lower/LazyGlue.lean`: `taskWaitAnyFn`.
- **Remove only if:** lean2rr generates a call with the list.

### A constant's walk for tasks waits in one pass

- **What:** The generated walk of a constant for its tasks (as native
  `lean_mark_persistent`) waits for each task as it reaches it, then
  looks into its value, in one pass. lean-runtime's `wait` runs the
  queue in the workers' order meanwhile (the awaited task only once a
  free worker would start it).
- **Why:** leanrt's own scheduler ran a task when it was waited for, so
  the walk had two passes: the first collected the tasks, and the second
  ran them in the workers' order before it waited (round 7 RV7L-06).
  lean-runtime's `wait` keeps that order itself (with one worker too: a
  pure task keeps its worker until it runs, lean-runtime's AR-25; tests
  `RtPersistOrder`, `RtPersistConv`, `RtPersistDropped`), and the walk
  marks what it visits persistent, which a second pass would then skip
  ([../startup/constants.md](../startup/constants.md)): the generator
  makes one pass, and the two passes' runtime functions (`collect`,
  `rewalk`, `before`, the generated `l2r_task_run_before`) are gone.
- **Where:** `Lower/Finish.lean`: `genPersist`, `finishPersistFns`;
  `runtime/leanrt/src/persist.rs` (module comment).
- **Remove only if:** lean-runtime's `wait` stops running the queue in
  the workers' order (then the order of the tasks a walk reaches would
  change).

### A priority is the whole value; above 8 is a dedicated task

- **What:** A priority is passed whole (`l2r_nat_sat(prio)`: its value,
  `u64::MAX` for 2^64 or more). leanrt keeps a dependent's priority until
  `depend` in its 40-byte entry as a `u32`, one of 2^32 or more as
  `u32::MAX`, which is above 8 too. lean-runtime's rule: 0 to 8 are the task
  manager's queues, every priority above 8 is a dedicated task (2^32-1,
  2^32 to 2^32+8 and a big `Nat` included). No priority makes a task
  `sync`: only `sync := true` does.
- **Why:** `Task.Priority`'s documentation: "Tasks with a priority greater
  than `Task.Priority.max` are scheduled on dedicated threads". Native Lean
  passes `lean_unbox(prio)` as an `unsigned`, so 2^32-1 is `LEAN_SYNC_PRIO`
  (the task runs at once on the enqueuing thread) and 2^32 to 2^32+8 are
  pool priorities: lean-runtime's LB-39, which lean2rr does not reproduce
  (switch step 13; before it, lean2rr took the priority modulo 2^32, adv4
  TK4-03, and the low 64 bits of a big `Nat`). Example: `IO.asTask (prio
  := 2^32 + 1)` while the one pool worker is busy runs at once on its own
  context; natively it waits in queue 1. Tests `RtTaskPrioBig`,
  `RtTaskPrioSync`.
- **Where:** `Lower/LazyGlue.lean`: `prioOf`; `runtime/leanrt/src/task.rs`:
  `Entry::prio`, `register`, `depend`; lean-runtime's
  `sched::common::priority`.
- **Remove only if:** never.

### `Task.get` in a `sync := true` task prints Lean's panic

- **What:** A wait for an unfinished task (`l2r_task_source_next_at`,
  `l2r_task_wait_running`) from a `sync := true` task first reports the
  Lean panic native `Task.get` prints (`GET_IN_SYNC_TASK`, through Lean's
  current stderr, or the process's under `LEAN_ABORT_ON_PANIC`:
  `leanrt::lean_panic`), then waits: lean-runtime's `await_task`, the rule
  both translators share.
- **Why:** As native `task_manager::wait_for` (lean-runtime's glue item
  3; cases `tasks/get_in_sync_task`, `get_in_sync_task_redirected`);
  leanrt's own scheduler did not print it.
- **Where:** `runtime/leanrt/src/task.rs`: `await_task`;
  `runtime/leanrt/src/lib.rs`: `lean_panic`; lean-runtime's
  `sched::await_task`.
- **Remove only if:** never.
