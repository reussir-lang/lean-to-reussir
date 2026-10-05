# The generated task primitives on lean-runtime's scheduler

Paths: `lean2rr/LeanToReussir/` for lean2rr's files, `runtime/` for the
runtime. Plan [§5.14](../../translation-plan.md#514-thunks-and-tasks)
("Tasks"). When a task runs (deferred until needed, the running code
blocking with a worker free, an effect point, polling, `main` returning),
which task a free worker takes, the pure-task rule, priorities, cancellation
and the final run are lean-runtime's rules (its `docs/sched.md`); the
entries here are how lean2rr's generated code reaches them.

### The generated code is unchanged; its primitives call lean-runtime

- **What:** The generated task code (creation `l2r_task_{defer,lazy,bind,
  lazybind}_S`, forcing `l2r_task_get_S`, the bind step, the dispatchers
  `l2r_task_run_one`, `l2r_task_force_sources`, `l2r_task_walk`,
  `l2r_run_pending_tasks`) is the one lean2rr generated for its own
  scheduler; its primitives (`l2r_task_*` in the prelude, `leanrt::task`)
  now map it onto lean-runtime's API: `register` is `spawn` (or, for a
  dependent, records the task until `depend_at`, which is `depend`);
  `source_next` and `wait_running` are `await_task` (`wait`, after
  `Task.get`'s panic in a `sync` task); `query` is `state`; `cancel_at`,
  `check_canceled`, `sleep_ms`, `shutdown` (`finish`) and `promise_new` are the calls of the
  same names; `deferring` is `manager_running`, read from the numbers
  `main`'s start read (lean-runtime starts at the first task:
  [scheduler.md](scheduler.md#lean-runtimes-scheduler-starts-at-the-first-task)).
  Answers the generated code
  no longer needs are constant: `register` and `depend` never ask it to run
  a task now (lean-runtime runs it inside the call), `end` never asks it to
  walk dependents, `walk_next` and, after `finish`, `next_tag` hand nothing.
- **Why:** One runtime (switch step 4): the scheduler is lean-runtime's.
  Keeping the generated code lets a program's code stay the same, task
  code included (the step's condition; the corpus's `.rr` outside the
  prelude is unchanged).
- **Where:** `runtime/leanrt/src/task.rs`; `runtime/prelude.rr` (the
  `l2r_task_*` textures); `Lower/LazyGlue.lean`, `Lower/LazyForce.lean`,
  `Lower/Promises.lean` (the generated code, unchanged).
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
  (`l2r_task_step_S`): the forcing code's question for the task's own
  sources (`source_next`) gets "none" (`run_cell`), `l2r_task_begin`
  answers whether it runs as on a worker thread (lean-runtime's
  `Glue::task_begin`), and `l2r_task_end` marks it finished for lean2rr
  (`DONE`). A bind task whose function returned an unfinished task reports
  it (`bind_wait`), and the job returns `Outcome::Continue` with a job for
  the continuation the generated code stored.
- **Why:** lean-runtime's jobs are boxed closures; lean2rr's tasks are
  run by generated code, which only the program's dispatcher can call
  (one entry point for every state type). The job and the entry are kept
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
  finish notifies nobody, as natively) and freed.
- **Why:** lean-runtime's glue item 3: "call `release(id)` for every
  task, IO tasks included" (a glue that skips it wakes waiters where
  native does not: cases `tasks/sync_walk_mutex_unref_finish`,
  `wait_any_unref_finish`). Lean deletes a pure task the program drops
  before a worker started it (adv4 TK4-01; leanrt's own scheduler read
  cell counts for it, `droppable_in`, which lean-runtime replaced with
  `release`).
- **Where:** `runtime/leanrt/src/task.rs`: `on_last_reference`, `unrun`,
  `JobRun`; `runtime/leanrt/src/drop.rs`: `free_cell`.
- **Remove only if:** never.

### `IO.waitAny`'s generated loop is mapped onto lean-runtime's `wait_any`

- **What:** The generated `IO.waitAny` asks `l2r_task_wait_status_at` for
  each task of the list, in a first pass (which takes a task answered 2)
  and a second (which runs a task answered 0), then calls
  `l2r_task_wait_progress` and starts over. The glue answers 1 to both
  passes while it collects the list (both passes: twice the list), then
  `wait_progress` calls lean-runtime's `wait_any` on it and the next first
  pass is answered 2 at the position lean-runtime chose. Positions, not
  addresses, are counted (a list may name a task twice). No context switch
  happens inside a pass; the state is set aside during lean-runtime's wait,
  where other contexts run their own `IO.waitAny`.
- **Why:** lean-runtime's `wait_any` takes the whole list and decides
  alone (its notification rule, RS2-06; what runs on the waiter's stack,
  AR-10); the generated code asks per task (unchanged, see the first entry).
- **Where:** `runtime/leanrt/src/task.rs`: `wait_status`,
  `wait_progress`, `WaitAny`; `Lower/LazyGlue.lean`: `taskWaitAnyFn`.
- **Remove only if:** lean2rr generates a call with the list.

### A constant's walk for tasks waits in one pass

- **What:** The generated walk of a constant for its tasks (as native
  `lean_mark_persistent`) waits for each task as it reaches it:
  `persist::collect` collects nothing, so the walk's first pass waits and
  looks into the values, and the second pass never runs (`rewalk` false,
  `before` none). lean-runtime's `wait` runs the queue in the workers'
  order meanwhile (the awaited task only once a free worker would start
  it).
- **Why:** leanrt's own scheduler ran a task when it was waited for, so
  the walk collected the tasks first and ran them in the workers' order
  (round 7 RV7L-06); lean-runtime's `wait` keeps that order itself (with
  one worker too: a pure task keeps its worker until it runs,
  lean-runtime's AR-25; tests `RtPersistOrder`, `RtPersistConv`,
  `RtPersistDropped`).
- **Where:** `runtime/leanrt/src/persist.rs`: `collect`, `rewalk`,
  `before`; `Lower/Finish.lean`: `genPersist`.
- **Remove only if:** lean2rr no longer generates the two passes.

### Priorities are taken modulo 2^32, as an `unsigned`

- **What:** A priority is passed as Lean passes it
  (`lean_usize_of_nat(prio)`); lean-runtime takes it modulo 2^32: 2^32-1
  (`LEAN_SYNC_PRIO`) runs at once on the enqueuing thread (a dependent as
  soon as its source finishes), 0 to 8 are the task manager's queues,
  above 8 is a dedicated thread.
- **Why:** Lean passes `lean_unbox(prio)` as an `unsigned` (adv4 TK4-03,
  5ec3ab9).
- **Where:** `Lower/LazyGlue.lean`: `prioOf`; lean-runtime's
  `sched::task::priority`.
- **Remove only if:** never.

### `Task.get` in a `sync := true` task prints Lean's panic

- **What:** A wait for an unfinished task (`l2r_task_force_sources`,
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
