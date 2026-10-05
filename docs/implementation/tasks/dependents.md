# Dependents: who runs when a task finishes

Paths: `lean2rr/LeanToReussir/` for lean2rr's files, `runtime/` for the
runtime. Plan [§5.14](../../translation-plan.md#514-thunks-and-tasks)
("Dependents", "Promises", and the end of "Blocking").

### `sync` dependents run on the finishing thread, walked by lean-runtime

- **What:** A task that waits for another (`mapTask`, `bindTask`,
  `Task.map`, `Task.bind`) is lean-runtime's dependent (`depend`). When its
  source finishes (its job returns, or a promise is resolved), lean-runtime
  walks the source's dependents newest first: a `sync := true` one (or one
  at priority 2^32-1) runs there and then, on the finishing context, the
  others are queued; waiters wake at the end of the walk. `sync := true` on
  a finished task applies `f` at once in the calling thread (generated
  code, as lean-runtime's `dependent_runs_now`). The `sync` dependents
  run with the streams the task left: a pool task's walk comes after its
  job, with its worker's stream cells still installed; a dedicated task's
  comes inside its job, before the generated code closes its fresh stream
  context (`end_running_task`,
  [scheduler.md](scheduler.md#each-context-pool-worker-and-dedicated-task-has-its-own-standard-streams)).
- **Why:** As Lean's `handle_finished` and `lean_task_map_core` (adv3
  P3-2, 946a9d0; adv4 TK4-05, 5ec3ab9); lean-runtime's model. The stream
  context: natively they run on the finishing worker thread with its
  current streams, the task's own if it set some and did not restore them
  (lean-runtime's AR-24, AR-26; test `RtTaskSyncStream`).
- **Where:** lean-runtime's `sched::task` (`walk_loop`, `end`,
  `end_running_task`); `runtime/leanrt/src/task.rs`: `depend`, `end`;
  `Lower/LazyGlue.lean`: `taskDepend`.
- **Remove only if:** never.

### A bind task waits for the task it continues as

- **What:** A bind task (`IO.bindTask`, `Task.bind`) runs `f`; if the task
  `f` returned has finished, it finishes with its value; otherwise the
  generated code stores a continuation reading that task's value
  (`pending`) and calls `l2r_task_bind_wait`, and the task's job returns
  `Outcome::Continue`: lean-runtime makes it wait for that task, keeping
  its priority and `sync` flag, and runs the continuation's job then.
- **Why:** As Lean's `task_bind_fn1` (f9e06af; adv4 TK4-06, 5ec3ab9).
- **Where:** `Lower/LazyForce.lean`: `taskBindStepFn`;
  `runtime/leanrt/src/task.rs`: `bind_wait`, `run_job`.
- **Remove only if:** never.

### No context is ever suspended inside a free

- **What:** A free's pending work is the thread's (`reussir_rt::drop`,
  patch 0014), so nothing that may block runs there: the drop of a stream
  handle runs in a no-suspend scope of lean-runtime's scheduler
  (`sched::no_suspend`: a dropped stream's flush writes what the descriptor
  takes and hands the rest to a writer thread), a task's release never
  waits, and a promise whose last reference goes inside
  a free (held by an array, list, map, structure or `Option` being freed)
  is resolved with `none` in its turn (its cell, stored in the no-suspend
  scope too: the store is a publication, which would wait for the
  context's handed-off streams; `task::drop_promise_now`), but resolved in
  lean-runtime, which walks its dependents (Lean code that may block),
  only once the free is over (`task::run_later`).
- **Why:** The other contexts would push their frees onto the suspended
  one's (2d21a0a: one free stack shared with Reussir's glue); lean-runtime's
  glue item 11, which asks for its no-suspend scope over the whole free
  path (review RSIO-03; RS4-04, test `RtPromiseDropInFreeWait`: a
  promise's store inside a free waited for a stream's writer, and another
  task's drop then went onto the suspended free).
- **Where:** `runtime/leanrt/src/drop.rs`: `run`; `runtime/leanrt/src/fs.rs`:
  `FileHandle`'s drop, `close`; `runtime/leanrt/src/task.rs`: `resolve`,
  `Promise` (`Drop`), `drop_promise_now`.
- **Remove only if:** never.

### Dependents of a promise dropped inside a free run when the free is over

- **What:** The kept resolutions run as soon as the free is over: when a
  free one of the runtime's containers started ends (`drop::run`), and,
  for a free Reussir's record glue started,
  through `__reussir_drop_drained`, a hook every outermost drain that
  released something calls when it ends (local Reussir patch 0040;
  `task::resolve` stores `task::drained` there). The symbol is linked
  weakly: without the patch, they run at the context's next task
  primitive, `Std.Sync` operation or constant claim. The `Std.Sync`
  primitives and `once::claim` run them before looking at their object; the
  generated code's wait for a task's own sources, right after a job handed
  the task over, does not (no other job may run before the task begins).
  Each context resolves only its own frees' promises, in order: it first
  takes them out of the list, so the next one waits until the dependents
  of the one before have run to their end, while a free inside such a
  dependent puts its own promises on the emptied list and resolves them
  when it ends, before the dependent goes on. `task::settled` counts the
  ones taken out and not resolved yet.
- **Why:** Natively the dependents run at once, on the dropping thread:
  code in between saw the old state, and their output escaped
  `IO.FS.withIsolatedStreams` (round 7 RV7C-01). A walk run after a
  `Std.Sync` caller had put the context in the object's waiter list woke
  the running context (a no-op) and it waited forever (RV7C-02; d5169c4;
  tests `RtPromiseFreeSync`, `RtSyncLostWake`). A reference's `set` frees
  the old value inside a free the runtime starts, so its walks run when
  that free ends, with or without 0040 (round 8 RV8T-01, 8af8f1a; test
  `RtPromiseFreeGlue`, see
  [../ownership.md](../ownership.md#reference-sets-store-the-new-value-before-releasing-the-old-one)).
  Natively a free inside a dependent is a free of its own, whose promises'
  dependents run inside it: a guard that kept nested calls from resolving
  anything left them for the end of the outer free's list (switch step 4;
  judge nested-free, test `RtPromiseNestedFreeOrder`).
- **Where:** `runtime/leanrt/src/task.rs`: `resolve`, `run_later`,
  `hook_drained`, `await_task`; `runtime/leanrt/src/drop.rs`: `run`;
  `runtime/leanrt/src/sync.rs`: `settle`; `runtime/leanrt/src/once.rs`:
  `claim`.
- **Remove only if:** never; the fallback stays as long as Reussir builds
  without patch 0040 are supported. Remaining difference: the
  dependents see the rest of the container released too (plan
  [§10](../../translation-plan.md#10-known-divergences-and-unsupported-features),
  "Promises released inside a free").
