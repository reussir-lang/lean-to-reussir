# Thunks, tasks and promises as cells

Paths: `lean2rr/LeanToReussir/` for lean2rr's files, `runtime/` for the
runtime. Plan [§5.14](../../translation-plan.md#514-thunks-and-tasks).

### A thunk or task is a cell holding a generated state

- **What:** `Thunk α` and `Task α` are `LCell<S>`, one runtime cell (a
  count and one value, seen through every alias) holding a generated
  shared enum `S { pending(L2RUnit -> Box), busy, done(Box) }`, one for
  thunks and one for tasks (tasks also `bind(…)`), whatever `α` is: the
  value is boxed, so typed and uniform code share every cell and nothing
  converts one. A shared enum holds closures too.
  `Thunk.mk f` is `pending(f)` (`f` wrapped to return a `Box`),
  `Thunk.pure a` is `done(a)` (boxed); `Thunk.get` swaps in `busy`, runs
  the closure, stores `done(v)`, and its caller unboxes `v`. The cell is
  lean-runtime's "translator's slot" of the task: the value lives there,
  and the slot comes first (once the cell holds `done`, the task has
  finished for lean2rr).
- **Why:** A thunk was a one-field struct holding its closure, so
  `Thunk.get` re-ran it every time (03bbbfd). A Reussir cell cannot hold a
  closure directly. With a state type per value type, a thunk or task
  crossing between typed and uniform code needed a converted copy (a
  `conv` state forcing the original, its own identity, and a task's
  address recorded for the runtime). Cost: `Thunk.mk` allocates one object
  more than Lean (the `pending` state).
- **Where:** `LowerBase.lean`: `lazyState` (`thunkState`, `taskState`),
  `lazyOf?`;
  `Lower/LazyForce.lean`: `lazyGetFn`, `lazyDone`, `lazyFn`;
  `Lower/LazyGlue.lean`: `lazyExtern`, `lazyExternGlue`;
  `runtime/prelude.rr`: `LCell`, `l2r_lcell_new`, `l2r_lcell_swap`;
  `runtime/leanrt/src/drop.rs`: `Cell` (its release and `l2r_lcell_get`'s
  `cell_get` test `count == 1`, the read releasing the cell before it
  copies the state, so that LLVM cancels the caller's increment:
  [../representations/arrays.md](../representations/arrays.md#a-release-tests-count--1)).
- **Remove only if:** never.

### A store into a cell is a publication

- **What:** `l2r_lcell_set` (a thunk's or task's value, a bind task's
  continuation) first calls lean-runtime's `sched::before_publish()`: the
  writer threads of the streams the running context's drops handed off end
  first (one relaxed load when there is none). A promise's resolution
  stores inside lean-runtime's `resolve`, after that call's own writers
  point (next entries).
- **Why:** lean-runtime's glue duty (its `docs/sched.md`, "The glue",
  items 3, 7 and 11): natively the dropping thread was inside those
  streams' `fclose` until then, so whoever sees the value sees their bytes
  delivered.
- **Where:** `runtime/prelude.rr`: `l2r_lcell_set`;
  `runtime/leanrt/src/sched.rs`: `before_publish`.
- **Remove only if:** never.

### A busy thunk is waited for; one needed by its own computation waits forever

- **What:** Forcing a `busy` thunk waits until it has its value, through
  lean-runtime's keyed wait cores (core 3.1), under the thunk's address:
  `l2r_thunk_wait_busy` is `wait_running_keyed` (the context registers as
  a waiter and blocks with `block_sync`), and `l2r_thunk_done`, after the
  store (`l2r_lcell_set`, which makes the writers point), is `done_keyed`
  (one thread-local load when none waits; otherwise the waiters wake in the
  order they began to wait). On another context it waits for the one
  forcing it; on the context that is computing it nothing ever wakes it,
  so it waits forever while the others go on; before the task manager runs,
  or with no other context, the thread hangs (`sched::hang`). The generated
  `busy` state names no forcer, so the generated code is unchanged
  (lean-runtime's unrecorded runner; lean2rr's L3).
- **Why:** Natively Lean spins forever on its own thunk (LB-08); another
  thread waits for the one forcing it (6f14a9e). lean-runtime's glue item
  7; the wait itself is lean-runtime's since switch step 6 (the owner's
  rule: runtime logic lives in lean-runtime once).
- **Where:** `Lower/LazyForce.lean`: `lazyGetFn`; `runtime/prelude.rr`:
  `l2r_thunk_wait_busy`, `l2r_thunk_done`; `runtime/leanrt/src/sched.rs`:
  `thunk_wait_busy`, `on_finish`.
- **Remove only if:** never.

### A cell names its task in lean-runtime through its padding

- **What:** lean-runtime names a task with a `TaskId`. A cell that is a
  task lean-runtime has not finished has an entry in `leanrt::task`'s slab
  (its `TaskId`, the task state type's tag, flags); the entry's index is stored
  in the 4 bytes of padding after the cell's count (`l2r_lcell_new`
  initializes it to "none"). A task is found by its cell's address. Once the cell holds `done`, its id is
  never given out again (`TaskId::FINISHED` instead: lean-runtime reuses
  entries and, after 2^32 tasks, generations).
- **Why:** The generated code names tasks by address (unchanged from
  leanrt's own scheduler, so the program's code is the same); a lookup by
  the padding is O(1) (BTreeMaps were slow: adv4 TK4-08, 5ec3ab9).
  lean-runtime's rule that the glue's slot comes first (its
  `docs/sched.md`, "The glue", item 3).
- **Where:** `runtime/leanrt/src/task.rs` (module comment): `init_cell`,
  `find`, `alloc`, `id_of`; `Lower/LazyForce.lean`: `taskAddr`.
- **Remove only if:** never.

### A promise is a runtime object holding a task over `Option Box`

- **What:** `IO.Promise α` (`lcAny` in mono code) is an `LPromise` holding
  the cell of a task over `Option Box`, whatever `α` is; lean-runtime's
  promise id (`sched::promise_new`) is that task's. `resolve` is
  lean-runtime's `resolve` (`l2r_promise_resolve_with`,
  `task::resolve_with`): after its writers point, and only for an
  unresolved promise, its store frees the promise's entry and stores
  `done(some v)` in the cell (only the first resolution counts), then
  lean-runtime walks the task's dependents on the resolving thread; the
  old state is released after the walk. `result?` gives the task as it is (one task type);
  `result!` maps `Option.getOrBlock!` over it. Dropping the last reference
  to an unresolved promise resolves it with `none` (the runtime calls the
  program's `l2r_promise_drop_c`). `IO.Promise.new` during initialization
  is Lean's internal panic (lean-runtime's `PROMISE_BEFORE_MANAGER`).
- **Why:** Typed and uniform code share one promise; native semantics
  (`resolve_core`, `deactivate_promise`) (4f8f6f1). The test and the store
  are made inside lean-runtime's `resolve` (lean-runtime's glue item 4):
  until switch step 14 the generated code tested the cell, then the
  store's publication (a writers point) let another context resolve the
  promise, and the store replaced that resolution (review HR-01, test
  `RtHandOffResolveAgain`: "main sees (some 1)" where native's is
  `some 2`). Lean's docs: "Only the first call to this function has an
  effect".
- **Where:** `Lower/Promises.lean`: `promiseTask`, `promiseResolveFn`,
  `promiseExtern`; `runtime/prelude.rr`: `l2r_promise_resolve_with`;
  `runtime/leanrt/src/task.rs`: `promise_new`, `promise_cell`,
  `resolve_with`.
- **Remove only if:** never.

### `Promise.result!` of a dropped promise blocks only its reader

- **What:** `Option.getOrBlock!` on `none` is lean-runtime's
  `option_get_or_block`: Lean's forced panic message (`lean_panic(msg,
  force_stderr)`: an effect point, C's `stdout` flushed, the line on the
  process's stderr, then the plan's abort or exit), the waiters of the
  walks in progress on this context wake (LB-32), then the running context
  waits forever (`sched::hang`); the other tasks and `main` go on.
- **Why:** It slept the OS thread, so no other context ever ran again;
  natively only the calling thread blocks (round 7 RV7C-03, 7a265db; test
  `RtPromiseResultDropped`; lean-runtime's cases `tasks/result_bang_*`).
- **Where:** `runtime/prelude.rr`: `l2r_option_get_or_block_none`;
  `runtime/leanrt/src/lib.rs`: `promise_dropped`, `lean_panic`.
- **Remove only if:** never.
