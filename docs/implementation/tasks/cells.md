# Thunks, tasks and promises as cells

Paths: `lean2rr/LeanToReussir/` for lean2rr's files, `runtime/` for the
runtime. Plan [§5.14](../../translation-plan.md#514-thunks-and-tasks).

### A thunk or task is a cell holding a generated state

- **What:** `Thunk α` and `Task α` are `LCell<S>`, one runtime cell (a
  count and one value, seen through every alias) holding a generated
  shared enum `S { pending(L2RUnit -> α), busy, done(α), conv(…) }`, one
  per value type and kind (tasks also `bind(…)`). A
  shared enum fits every `α`, closures and value types included.
  `Thunk.mk f` is `pending(f)`, `Thunk.pure a` is `done(a)`; `Thunk.get`
  swaps in `busy`, runs the closure, stores `done(v)`. The cell is
  lean-runtime's "translator's slot" of the task: the value lives there,
  and the slot comes first (once the cell holds `done`, the task has
  finished for lean2rr).
- **Why:** A thunk was a one-field struct holding its closure, so
  `Thunk.get` re-ran it every time (03bbbfd). A Reussir cell cannot hold a
  closure directly. Cost: `Thunk.mk` allocates one object more than Lean
  (the `pending` state).
- **Where:** `LowerBase.lean`: `lazyState`, `lazyOf?`;
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
  continuation, a promise's resolution) first calls lean-runtime's
  `sched::before_publish()`: the writer threads of the streams the running
  context's drops handed off end first (one relaxed load when there is
  none).
- **Why:** lean-runtime's glue duty (its `docs/sched.md`, "The glue",
  items 3, 7 and 11): natively the dropping thread was inside those
  streams' `fclose` until then, so whoever sees the value sees their bytes
  delivered.
- **Where:** `runtime/prelude.rr`: `l2r_lcell_set`;
  `runtime/leanrt/src/sched.rs`: `before_publish`.
- **Remove only if:** never.

### A busy thunk is waited for; one needed by its own computation waits forever

- **What:** Forcing a `busy` thunk waits until it has its value
  (`l2r_thunk_wait_busy`: the context registers as a waiter of the thunk's
  address and blocks with lean-runtime's `block_sync`; `l2r_thunk_done`
  wakes the waiters with `wake`). On another context it waits for the one
  forcing it; on the context that is computing it nothing ever wakes it,
  so it waits forever while the others go on (before `main`: the thread
  waits forever, `sched::hang`).
- **Why:** Natively Lean spins forever on its own thunk (LB-08); another
  thread waits for the one forcing it (6f14a9e). lean-runtime's glue item 7.
- **Where:** `Lower/LazyForce.lean`: `lazyGetFn`; `runtime/prelude.rr`:
  `l2r_thunk_wait_busy`, `l2r_thunk_done`; `runtime/leanrt/src/sched.rs`:
  `thunk_wait_busy`, `on_finish`.
- **Remove only if:** never.

### A cell names its task in lean-runtime through its padding

- **What:** lean-runtime names a task with a `TaskId`. A cell that is a
  task lean-runtime has not finished has an entry in `leanrt::task`'s slab
  (its `TaskId`, its state type's tag, flags); the entry's index is stored
  in the 4 bytes of padding after the cell's count (`l2r_lcell_new`
  initializes it to "none"). A task is found by an address: its cell's, or
  the one a converted task records. Once the cell holds `done`, its id is
  never given out again (`TaskId::FINISHED` instead: lean-runtime reuses
  entries and, after 2^32 tasks, generations).
- **Why:** The generated code names tasks by address (unchanged from
  leanrt's own scheduler, so the program's code is the same); a lookup by
  the padding is O(1) (BTreeMaps were slow: adv4 TK4-08, 5ec3ab9).
  lean-runtime's rule that the glue's slot comes first (its
  `docs/sched.md`, "The glue", item 3).
- **Where:** `runtime/leanrt/src/task.rs` (module comment): `init_cell`,
  `find`, `alloc`, `id_of`; `Lower/LazyForce.lean`: `taskAddrFn`.
- **Remove only if:** never.

### A promise is a runtime object holding a task over `Option Box`

- **What:** `IO.Promise α` (`lcAny` in mono code) is an `LPromise` holding
  the cell of a task over `Option Box`, whatever `α` is; lean-runtime's
  promise id (`sched::promise_new`) is that task's. `resolve` stores
  `some v` (only the first resolution counts) and then calls
  lean-runtime's `resolve`, which walks the task's dependents on the
  resolving thread; `result?` converts the task to `Task (Option α)`;
  `result!` maps `Option.getOrBlock!` over it. Dropping the last reference
  to an unresolved promise resolves it with `none` (the runtime calls the
  program's `l2r_promise_drop_c`). `IO.Promise.new` during initialization
  is Lean's internal panic (lean-runtime's `PROMISE_BEFORE_MANAGER`).
- **Why:** Typed and uniform code share one promise; native semantics
  (`resolve_core`, `deactivate_promise`) (4f8f6f1).
- **Where:** `Lower/Promises.lean`: `promiseTask`, `promiseResolveFn`,
  `promiseExtern`; `runtime/leanrt/src/task.rs`: `promise_new`,
  `promise_cell`, `resolve`.
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

### Converted cells

- **What:** A thunk or task at another representation is a `conv` cell
  that forces the original; it has no running state of its own, and a
  converted task names the original's address (its entry) to the runtime.
- **Why/Where:** see
  [../conversions/wrappers.md](../conversions/wrappers.md#thunks-and-tasks-convert-lazily-and-convert-back-to-the-original).
- **Remove only if:** see the linked entry.
