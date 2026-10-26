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
  run with the streams the task left: every task's walk comes after its
  job, before lean-runtime calls the glue's `task_end`, so a pool task's
  worker stream cells are still installed and a dedicated task's fresh
  stream context is still open (`task_end` closes it;
  [scheduler.md](scheduler.md#each-context-pool-worker-and-dedicated-task-has-its-own-standard-streams)).
  Until hunt HTG-01 a dedicated task's walk came inside its job
  (lean-runtime's `end_running_task`, from `task::end`): a rule from before
  review RS15-01, when the generated code closed that context inside the
  job.
- **Why:** As Lean's `handle_finished` and `lean_task_map_core` (adv3
  P3-2, 946a9d0; adv4 TK4-05, 5ec3ab9); lean-runtime's model. The stream
  context: natively they run on the finishing worker thread with its
  current streams, the task's own if it set some and did not restore them
  (lean-runtime's AR-24, AR-26; test `RtTaskSyncStream`).
- **Where:** lean-runtime's `sched::task` (`run_task_once`, `walk_loop`,
  `end`); `runtime/leanrt/src/task.rs`: `depend`, `end`;
  `runtime/leanrt/src/sched.rs`: `LeanrtGlue::task_end`;
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

- **What:** A free's pending work is the thread's (the stack of pending
  drops that Reussir's glue and leanrt share, `pending`, which every
  context of the thread shares too), so nothing that may block runs inside
  a drain, leanrt's or Reussir's glue's: the drop of a stream
  handle runs in a no-suspend scope of lean-runtime's scheduler
  (`sched::no_suspend`: a dropped stream's flush writes what the descriptor
  takes and hands the rest to a writer thread), a task's release never
  waits, and an unresolved promise whose last reference goes inside
  a drain (held by an array, a box, a reference's old value, or a
  list, map, structure, `Option` or tree that such a free releases)
  is resolved with `none` only once the free is over, its cell's store
  included (the store is a publication, which may wait for the context's
  handed-off streams, and the walk of its dependents runs Lean code, which
  may block): when the free reaches it, `task::defer_promise_drop` puts the
  whole resolution off with lean-runtime's `defer` (core 3.3) and asks for
  the free's end work (`pending::want_end_work`). A promise whose last
  reference goes outside a drain is resolved at once
  (`drop_promise_now`), also when Reussir's glue reaches it as it frees a
  record that user code drops outside a drain (a structure, a list, the
  root of a tree: no state of the glue is pending there). A resolved
  promise has nothing to resolve: when the free reaches it, its reference
  to its task's cell goes right there, so what the cell holds is released
  in the free's order, as natively (review RS6-01, test
  `RtPromiseResolvedFreeOrder`; its status cannot change between its drop
  and that step, since no Lean code runs in a free). No Lean
  code runs inside a drain, so none of lean-runtime's wait cores (a
  reference's, a thunk's, a constant's) is reached there (its W3; checked in
  debug builds, `drop::assert_not_in_free`; test `RtPromiseFreeDepWaits`;
  no context switches there either, checked in `LeanrtGlue::switched`).
- **Why:** The other contexts would push their frees onto the suspended
  one's (2d21a0a: one free stack per thread, then shared with Reussir's
  glue, then leanrt's own, now Reussir's drop stack shared again); lean-runtime's
  glue item 11, which asks for its no-suspend scope over the whole free
  path (review RSIO-03; RS4-04, test `RtPromiseDropInFreeWait`: a
  promise's store inside a free waited for a stream's writer, and another
  task's drop then went onto the suspended free). While Reussir's glue
  shared one stack with leanrt, a promise in a record that user code
  freed next to a pending list could be resolved at once with the outer
  free's entries still pending, and a free inside its dependents would
  drain them (audit Q6 of the destructor port, found by inspection; not
  reproduced). Now nothing is pending outside a drain, and the
  promise is resolved where Reussir's glue reaches it, in field order
  (plan
  [§10](../../translation-plan.md#10-known-divergences-and-unsupported-features),
  "Order of releases in one free"; test `RtPromiseDropRecordPending`, a
  `Holder` that user code frees: `q`'s dependent runs before `p`'s,
  natively after). On Reussir base l2r-base9 without local patches 23-k
  to 23-m, Reussir's drain kept its pending drops per thread beside
  leanrt's stack, and a promise dropped inside it (a tree's child that
  user code frees) was resolved at once, its `sync` dependents run inside
  the drain: their frees of such trees then joined the drain and waited
  for it, so a promise dropped there was not resolved (test
  `RtPromiseDepFreeInDrain`: `false`, natively `true`) and a dependent
  waiting for one hung (`RtPromiseDepWaitInDrain`). With one stack, the
  promise is put off as inside any drain. Reussir's drop functions carry
  `nocallback` and `willreturn`, and a dependent run there calls back
  into the program; LLVM ignores `nocallback` on a function defined in
  the module (audit Q4, checked on both Reussir bases: a probe whose hook
  writes a module global through an exported function reads it right
  after every drop).
- **Where:** `runtime/leanrt/src/drop.rs`: `run`, `active`,
  `assert_not_in_free`; `runtime/leanrt/src/pending.rs`: `releasing`,
  `want_end_work`; `runtime/leanrt/src/fs.rs`: `FileHandle`'s drop,
  `close`; `runtime/leanrt/src/task.rs`: `resolve_with`, `Promise`
  (`Drop`), `defer_promise_drop`, `drop_promise_now`;
  `runtime/leanrt/src/sched.rs`: `switched`.
- **Remove only if:** never.

### Dependents of a promise dropped inside a free run when the free is over

- **What:** The resolutions a free put off run as soon as it is
  over, in the order the free reached their promises, on the context that
  freed them (lean-runtime's `run_deferred`, core 3.3). The outermost
  drain (`pending::drain`, or a drain of Reussir's glue) ends with its end work when a release
  asked for it (`pending::want_end_work`, called by
  `task::defer_promise_drop` and by a close the free puts off):
  `task::drained` calls `run_deferred`, then lean-runtime's
  drain-end hook `after_drain` (the writers of the streams the context
  handed off end; each resolution waits only for those handed off before
  it, review RF14-07:
  [scheduler.md](scheduler.md#the-end-of-a-handles-free-waits-for-its-writer-lean-runtimes-drain-end-hook)).
  The end work runs with the stack empty and its flag clear, so it
  may start a new free and may switch contexts. So the deferred list is
  empty whenever the context could block or switch, and nothing else runs
  it (the settle points that ran it at the next task primitive,
  `Std.Sync` operation or constant claim, for frees whose end was not
  reported, are gone). Each resolution stores `none` in the promise's cell,
  then walks its dependents, so until its dependents run the promise looks
  unresolved, as natively, to the dependents of a promise the free reached
  before it and to the other contexts (the store-with-resolve shape of
  lean-runtime's R3, review RW1-05; test `RtPromiseFreeLaterUnresolved`). A free inside a dependent
  resolves its own promises at its own end, before the outer free's next
  promise (lean-runtime's R5).
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
  resolved yet. Every free's end must run them since step 6: otherwise a
  free's resolutions would wait for the context's next run of the list,
  and lean-runtime's debug builds report that (its R6). Until the port to
  upstream Reussir's drop design, Reussir reported the end of each drain
  through a local patch (a drain-end hook); leanrt's own stack has its
  own end, so lean2rr needs no Reussir hook.
- **Where:** `runtime/leanrt/src/task.rs`: `Promise` (`Drop`),
  `defer_promise_drop`, `resolve_with`, `drained`;
  `runtime/leanrt/src/pending.rs`: `drain`, `want_end_work`.
- **Remove only if:** never. Remaining differences: the
  dependents see the rest of the container released too (plan
  [§10](../../translation-plan.md#10-known-divergences-and-unsupported-features),
  "Promises released inside a free"); a promise that Reussir's glue
  reaches while it frees a record that user code drops is resolved at
  once, in field order ("Order of releases in one free").
