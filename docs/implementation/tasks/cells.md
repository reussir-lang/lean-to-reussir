# Thunks, tasks and promises as cells

Paths: `lean2rr/LeanToReussir/` for lean2rr's files, `runtime/` for the
runtime. Plan [§5.14](../../translation-plan.md#514-thunks-and-tasks).

### A thunk or task is a cell holding a generated state

- **What:** `Thunk α` and `Task α` are `LCell<S>`, one runtime cell (a
  count and one value, seen through every alias) holding a generated
  shared enum `S { pending(L2RUnit -> α), busy, done(α), conv(…),
  convdone(…) }`, one per value type and kind (tasks also `bind(…)`). A
  shared enum fits every `α`, closures and value types included.
  `Thunk.mk f` is `pending(f)`, `Thunk.pure a` is `done(a)`; `Thunk.get`
  swaps in `busy`, runs the closure, stores `done(v)`.
- **Why:** A thunk was a one-field struct holding its closure, so
  `Thunk.get` re-ran it every time (03bbbfd). A Reussir cell cannot hold a
  closure directly. Cost: `Thunk.mk` allocates one object more than Lean
  (the `pending` state).
- **Where:** `LowerBase.lean`: `lazyState`, `lazyOf?`;
  `Lower/LazyForce.lean`: `lazyGetFn`, `lazyDone`, `lazyFn`;
  `Lower/LazyGlue.lean`: `lazyExtern`, `lazyExternGlue`;
  `runtime/prelude.rr`: `LCell`, `l2r_lcell_new`, `l2r_lcell_swap`;
  `runtime/leanrt/src/drop.rs`: `Cell`.
- **Remove only if:** never.

### A thunk needed by its own computation waits forever

- **What:** Forcing a `busy` thunk waits until it has its value
  (`l2r_thunk_wait_busy`, a `sched::block` woken by `l2r_thunk_done`): on
  another context it waits for the one forcing it; on the context that is
  computing it nothing ever wakes it (before `main`, `task::hang`), so it
  waits forever, as Lean does. (A `busy` task waits through
  `l2r_task_wait_running` in the same way.)
- **Why:** Natively Lean spins forever on its own thunk; another thread
  waits for the one forcing it. The second case waited forever before the
  scheduler's second review (6f14a9e).
- **Where:** `Lower/LazyForce.lean`: `lazyGetFn`; `runtime/prelude.rr`:
  `l2r_thunk_wait_busy`, `l2r_thunk_done`; `runtime/leanrt/src/task.rs`:
  `thunk_wait_busy`, `hang`.
- **Remove only if:** never.

### The runtime finds a task's entry through the cell's padding

- **What:** `leanrt::task` keeps an entry per unfinished task in a slab;
  the entry's index is stored in the 4 bytes of padding after the cell's
  count (`l2r_lcell_new` initializes it). Dependents are intrusive lists,
  newest first; queues are per priority, stale items skipped and
  compacted. A task is identified by an address: its cell's, or the one a
  converted task records.
- **Why:** BTreeMaps per operation were slow (Tk4Fan1 565 → 90 ms;
  adv4 TK4-08, 5ec3ab9). Entries and cell addresses are reused, so forcing
  chains (a deadlock with an unbuffered channel, 97acbd0) and worker
  contexts (6f14a9e) recognize their tasks by the entry's serial number.
- **Where:** `runtime/leanrt/src/task.rs` (module comment): `init_cell`,
  `register`, `serial_of`, `source_next`; `Lower/LazyForce.lean`:
  `taskAddrFn`.
- **Remove only if:** never.

### A promise is a runtime object holding a task over `Option Box`

- **What:** `IO.Promise α` (`lcAny` in mono code) is an `LPromise` holding
  the cell of a task over `Option Box`, whatever `α` is. `resolve` stores
  `some v` (only the first resolution counts) and walks the task's
  dependents on the resolving thread; `result?` converts the task to
  `Task (Option α)`; `result!` maps `Option.getOrBlock!` over it. Dropping
  the last reference to an unresolved promise resolves it with `none`
  (the runtime calls the program's `l2r_promise_drop_c`).
  `IO.Promise.new` during initialization is Lean's internal panic.
- **Why:** Typed and uniform code share one promise; native semantics
  (`resolve_core`, `deactivate_promise`) (4f8f6f1).
- **Where:** `Lower/Promises.lean`: `promiseTask`, `promiseResolveFn`,
  `promiseExtern`; `runtime/leanrt/src/task.rs`: `promise_new`,
  `promise_cell`, `resolve`.
- **Remove only if:** never.

### `Promise.result!` of a dropped promise blocks only its reader

- **What:** `Option.getOrBlock!` on `none` prints Lean's panic message and
  then blocks the running context forever (`task::hang`); the other tasks
  and `main` go on. `LEAN_ABORT_ON_PANIC` still aborts.
- **Why:** It slept the OS thread, so no other context ever ran again;
  natively only the calling thread blocks (round 7 RV7C-03, 7a265db; test
  `RtPromiseResultDropped`).
- **Where:** `runtime/prelude.rr`: `l2r_option_get_or_block_none`;
  `runtime/leanrt/src/lib.rs`: `promise_dropped`;
  `runtime/leanrt/src/task.rs`: `hang`.
- **Remove only if:** never.

### Converted cells

- **What:** A thunk or task at another representation is a `conv` cell
  that forces the original; it has no running state of its own.
- **Why/Where:** see
  [../conversions/wrappers.md](../conversions/wrappers.md#thunks-and-tasks-convert-lazily-and-convert-back-to-the-original).
- **Remove only if:** see the linked entry.
