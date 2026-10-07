# Dependents: who runs when a task finishes

Paths: `lean2rr/LeanToReussir/` for lean2rr's files, `runtime/` for the
runtime. Plan [§5.14](../../translation-plan.md#514-thunks-and-tasks)
("Dependents", "Promises", and the end of "Blocking").

### `sync` dependents run on the finishing thread, walked by lean-runtime

- **What:** A task that waits for another (`mapTask`, `bindTask`,
  `Task.map`, `Task.bind`) is lean-runtime's dependent (`depend`). When its
  source finishes (its job returns, or a promise is resolved), lean-runtime
  walks the source's dependents newest first: a `sync := true` one runs
  there and then, on the finishing context, the
  others are queued; waiters wake at the end of the walk. `sync := true` on
  a finished task applies `f` at once in the calling thread (generated
  code, as lean-runtime's `dependent_runs_now`). If the source finishes
  after that test, during `depend`'s writers point, lean-runtime runs a
  `sync` dependent inside `depend` (its job stores the value in the cell
  and frees the entry, so leanrt keeps no id and answers 0: nothing runs
  twice, and no `sync` task is queued). It runs as Lean's fast path, the
  caller's code (`lean_task_map_core` applies the function at once when
  the source has finished, as natively it had before the close that
  delayed it here returned), so a `Task.get` in it prints the
  "`Task.get` called from a `(sync := true)` task" panic only where the
  caller is a `sync` task (lean-runtime's HR-02 and RF14-03, since switch
  step 14; before, it queued the `sync` dependent, which later printed
  that panic when it waited). leanrt holds no reference into its entries across
  `depend`, where the job may add entries. The `sync` dependents
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
  its priority and `sync` flag, and runs the continuation's job then. The
  task may finish after the generated test (the continuation's store is a
  publication, where other contexts run): `bind_wait` then passes the
  finished task (`TaskId::FINISHED`), and lean-runtime runs a `sync` bind
  task's continuation at once, on the thread of its first run, and queues an async one
  (lean-runtime's HR-02, since switch step 14; before, it queued the
  `sync` one too).
- **Why:** As Lean's `task_bind_fn1` (f9e06af; adv4 TK4-06, 5ec3ab9).
- **Where:** `Lower/LazyForce.lean`: `taskBindStepFn`;
  `runtime/leanrt/src/task.rs`: `bind_wait`, `run_job`.
- **Remove only if:** never.

### No context is ever suspended inside a free

- **What:** A free's pending work is the thread's (`reussir_rt::drop`,
  patch 13-b), so nothing that may block runs there: the drop of a stream
  handle runs in a no-suspend scope of lean-runtime's scheduler
  (`sched::no_suspend`: a dropped stream's flush writes what the descriptor
  takes and hands the rest to a writer thread), a task's release never
  waits, and an unresolved promise whose last reference goes inside
  a free (held by an array, list, map, structure or `Option` being freed)
  is resolved with `none` only once the free is over, its cell's store
  included (the store is a publication, which may wait for the context's
  handed-off streams, and the walk of its dependents runs Lean code, which
  may block): when the free reaches it, `task::defer_promise_drop` puts the
  whole resolution off with lean-runtime's `defer` (core 3.3). A resolved
  promise has nothing to resolve: when the free reaches it, its reference
  to its task's cell goes right there, so what the cell holds is released
  in the free's order, as natively (review RS6-01, test
  `RtPromiseResolvedFreeOrder`; its status cannot change between its drop
  and that step, since no Lean code runs in a free). No Lean
  code runs inside a free, so none of lean-runtime's wait cores (a
  reference's, a thunk's, a constant's) is reached there (its W3; checked in
  debug builds, `drop::assert_not_in_free`; test `RtPromiseFreeDepWaits`).
- **Why:** The other contexts would push their frees onto the suspended
  one's (2d21a0a: one free stack shared with Reussir's glue); lean-runtime's
  glue item 11, which asks for its no-suspend scope over the whole free
  path (review RSIO-03; RS4-04, test `RtPromiseDropInFreeWait`: a
  promise's store inside a free waited for a stream's writer, and another
  task's drop then went onto the suspended free).
- **Where:** `runtime/leanrt/src/drop.rs`: `run`, `assert_not_in_free`;
  `runtime/leanrt/src/fs.rs`: `FileHandle`'s drop, `close`;
  `runtime/leanrt/src/task.rs`: `resolve_with`, `Promise` (`Drop`),
  `defer_promise_drop`, `drop_promise_now`.
- **Remove only if:** never.

### Dependents of a promise dropped inside a free run when the free is over

- **What:** The resolutions a free put off run as soon as it is over, in
  the order the free reached their promises, on the context that freed
  them (lean-runtime's `run_deferred`, core 3.3): Reussir reports the end
  of every drain that released something through `__reussir_drop_drained`
  (local Reussir patch 40-a), where `task::hook_drained` stores
  `task::drained`, which calls `run_deferred`, then lean-runtime's
  drain-end hook `after_drain` (the writers of the streams the context
  handed off end; each resolution waits only for those handed off before
  it, review RF14-07:
  [scheduler.md](scheduler.md#the-end-of-a-handles-free-waits-for-its-writer-lean-runtimes-drain-end-hook)).
  lean2rr requires the patch: `scripts/l2r.py` stops with
  an error when the Reussir checkout lacks it, and leanrt names the symbol,
  so it would not link either. So the deferred list is empty whenever the
  context could block or switch, and nothing else runs it (the settle
  points that ran it at the next task primitive, `Std.Sync` operation or
  constant claim, for frees whose end a Reussir without the patch did not
  report, are gone). Each resolution stores `none` in the promise's cell,
  then walks its dependents, so until its dependents run the promise looks
  unresolved, as natively, to the dependents of a promise the free reached
  before it and to the other contexts (the store-with-resolve shape of
  lean-runtime's R3, review RW1-05; test `RtPromiseFreeLaterUnresolved`). A free inside a dependent
  resolves its own promises at its own end, before the outer free's next
  promise (lean-runtime's R5). `task::settled` asks lean-runtime's
  `deferred_pending`, which counts a resolution under way too.
- **Why:** Natively the dependents run at once, on the dropping thread:
  code in between saw the old state, and their output escaped
  `IO.FS.withIsolatedStreams` (round 7 RV7C-01). A walk run after a
  `Std.Sync` caller had put the context in the object's waiter list woke
  the running context (a no-op) and it waited forever (RV7C-02; d5169c4;
  tests `RtPromiseFreeSync`, `RtSyncLostWake`). A reference's `set` frees
  the old value inside a free the runtime starts, so its walks run when
  that free ends (round 8 RV8T-01, 8af8f1a; test
  `RtPromiseFreeGlue`, see
  [../ownership.md](../ownership.md#reference-sets-store-the-new-value-before-releasing-the-old-one)).
  Natively a free inside a dependent is a free of its own, whose promises'
  dependents run inside it (judge nested-free, test
  `RtPromiseNestedFreeOrder`). The protocol is lean-runtime's since switch
  step 6 (the owner's rule: runtime logic lives in lean-runtime once); with
  the store made in the drain (lean2rr's shape before), the dependents of
  an earlier promise of the same free, and another context while they
  blocked, saw a later promise finished, where natively it was not
  resolved yet. Patch 40-a is
  required since step 6: without it a drain's resolutions would wait for
  the context's next run of the list, and lean-runtime's debug builds report
  that (its R6).
- **Where:** `runtime/leanrt/src/task.rs`: `Promise` (`Drop`),
  `defer_promise_drop`, `resolve_with`, `hook_drained`, `drained`, `settled`;
  `scripts/l2r.py`: `REQUIRED_REUSSIR_PATCHES`, `check_reussir_patches`.
- **Remove only if:** never. Remaining difference: the
  dependents see the rest of the container released too (plan
  [§10](../../translation-plan.md#10-known-divergences-and-unsupported-features),
  "Promises released inside a free").
