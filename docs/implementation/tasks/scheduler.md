# The scheduler

A thread that blocks natively (a lock, a condition variable, a task or
promise not finished yet, a sleep, a socket, a read of an empty pipe) lets
others go on. lean-runtime's scheduler reproduces that on one thread with
*contexts* (its `docs/sched.md`: corosensei coroutines, every switch
through `main`'s stack, the hub's order, effect and polling points, the
event loop). Paths: `runtime/leanrt/src/` unless they say otherwise. Plan
[§5.14](../../translation-plan.md#514-thunks-and-tasks) ("Blocking").

### The glue's one `unsafe` step: the suspend

- **What:** lean-runtime's `Glue::suspend` is the translator's: it
  dereferences the running coroutine's yielder (`(*s.yielder()).suspend(())`)
  and nothing else. Its `SAFETY` entry gives the argument (lean-runtime's
  S1-S7: the pointer is the running context's own, read in the borrow that
  blocks it, valid until the coroutine returns, never force-unwound) and
  lean2rr's duties: the pointer is never kept or copied, no scheduler
  function is called from a signal handler, another thread or a stack of
  lean2rr's own (it has none), `switched` only moves state, `start` runs
  on `main`'s thread.
- **Why:** corosensei hands the yielder only to the coroutine's entry, and
  the code that blocks is deep in the translated program; safe Rust cannot
  express the step, so lean-runtime (`forbid(unsafe_code)`) leaves it to
  each translator's glue with a full documented entry (owner's decision,
  2026-10-03; lean-runtime's "Why `Glue::suspend` is sound").
- **Where:** `sched.rs`: `LeanrtGlue::suspend`; lean-runtime's
  `src/sched/ctx.rs` (`switch_away`).
- **Remove only if:** corosensei (or another vetted crate) offers a safe
  suspend from nested code.

### Contexts are lean-runtime's

- **What:** `main`'s context runs on its thread's stack; each task
  lean-runtime starts gets a corosensei stack of a native worker's size
  (1 GiB, or `LEAN_STACK_SIZE_KB` rounded down to 4 KiB plus 128 KiB),
  mapped `PROT_NONE` with all but one guard page made writable, touched
  only as used; up to 8 ended contexts' stacks are kept for reuse with the
  pages they touched. A task that is needed runs on the stack of whoever
  needs it once a free worker would start it (lean-runtime's
  `may_run_awaited`), also a pure task that the worker woken by an
  earlier enqueue starts during the wait's own look (`settle_worker`,
  then `pick`; lean-runtime's fixes-8, 83f7127, switch step 9: before it,
  the waiter blocked after `pick`'s wake-up had gone by, and with a
  descriptor watched nothing ran the task, so the program hung; test
  `RtTaskPickedInWait`, [../externs-ffi/runtime.md](../externs-ffi/runtime.md)).
  The number of workers is `LEAN_NUM_THREADS` (glibc's
  `atoi`) or the online processors (`std::thread::hardware_concurrency`);
  0 is no task manager (tasks run at once).
- **Why:** lean-runtime's model (its `docs/sched.md`, "The model",
  "Differences from lean2rr's runtime": leanrt's own contexts switched
  stacks with hand-written assembly and reserved them `MAP_NORESERVE`,
  released with `madvise` when pooled).
- **Where:** lean-runtime's `src/sched/ctx.rs`, `env.rs`; `sched.rs`:
  `start`, `hardware_concurrency`.
- **Remove only if:** the runtime gets real threads.

### Each context, pool worker and dedicated task has its own standard streams

- **What:** The current standard streams of `IO.setStdout` & co. are
  lean2rr's mutable once-cells. At every switch the glue sets the leaving
  context's cells and saved stream contexts aside and gives the arriving
  context its own (`Glue::switched`, over `once::swap_ctx_state`; a new
  context starts with empty cells, rebuilt as the process's streams on
  first use). A task that natively runs on a thread of its own
  (lean-runtime's `Glue::task_begin(own_thread)`):
  - a pool task runs with its emulated worker's cells (lean-runtime's
    `running_worker()`, the lowest worker id no running task holds): they
    come in at `task_begin` (`once::swap_cells`; empty for the worker's
    first task) and stay installed through the walk of its `sync`
    dependents; at `task_end` the worker keeps what the task left and the
    running thread's cells come back;
  - a dedicated task opens a fresh stream context and closes it at its end
    (`l2r_task_begin` answers `B_ENTER`: `l2r_std_enter_if`/
    `l2r_std_leave_if` over `once::push_context`/`pop_context`); right
    before the close, `l2r_task_end` ends the task in lean-runtime
    (`end_running_task(id)`, with the id `spawn` or `depend` returned, kept
    in the task's entry before anyone else gets it; not while a bind
    continuation is pending), so its `sync` dependents run inside its
    context;
  - a task on the current thread (a `sync` dependent, priority 2^32-1)
    shares that thread's cells.
  When the task manager's finalization ends its standard workers
  (lean-runtime's `Glue::workers_end`: no pool task is queued or running
  any more, and the dedicated tasks are not waited for yet), the generated
  `l2r_std_drop_workers` (in a program that creates tasks; the runtime
  calls it through its trampoline) drops each worker's cells in worker
  order (`sched::worker_streams_enter` makes them current, the generated
  `l2r_std_leave` drops them): a handle a worker's task left as its stdout
  is closed, so its buffered bytes come before `main`'s stdout is flushed
  at exit, and a pipe it held is closed before a dedicated task waits for
  its reader. A pool task that begins afterwards (a dedicated task's
  dependent) gets a fresh stream context, closed at its end, as a
  dedicated task. `IO.Process.exit` drops nothing (natively it runs no
  thread finalizers). Panics, `dbgTrace` and `timeit` write through the current
  stderr stream (`l2r_stderr_put`).
- **Why:** Natively `IO.setStdout` & co. replace the current thread's
  streams; a pool worker keeps them from one task to the next, a task's
  `sync` dependents run on its thread with what it left, a dedicated task
  has a thread of its own, and the task manager's finalization joins the
  workers, whose thread finalizers drop their streams (adv2 EFF-1, f9e06af;
  lean-runtime's AR-24, AR-26, AR-32, AR-33, AR-34; tests
  `RtTaskSyncStream`, lean-runtime's cases `tasks/worker_keeps_streams`,
  `worker_streams_closed_at_exit`, `worker_streams_at_process_exit`,
  `worker_streams_before_dedicated`).
  lean-runtime keeps its own per-worker state (`io::streams`, `errno`)
  itself; lean2rr's stream cells are values only its generated code can
  build and drop, so the glue keeps them per worker id. A context's record
  outlives it and is given to a new context that reuses its id
  (lean-runtime's `CtxId`s are reused and the glue hears of no context's
  end). The event loop's context follows the same rule: its stream cells
  are those of its `CtxId`, where lean-runtime keeps one set for the loop
  and gives it to the next loop context. A `sync` dependent of a promise
  the loop resolves that sets a standard stream and does not restore it
  leaves it to a later loop context only when that context gets the same
  id (review RS4-06; only such a program can see it).
- **Where:** `sched.rs`: `LeanrtGlue::switched`, `task_begin`, `task_end`,
  `workers_end`, `fresh_context`, `worker_streams_enter`; `task.rs`:
  `begin`, `end`;
  `once.rs`: `swap_ctx_state`, `swap_cells`, `enter_cells`,
  `push_context`, `pop_context`; `runtime/prelude.rr`:
  `l2r_worker_streams_enter`; `lean2rr/LeanToReussir/Lower/Externs.lean`:
  `stdContextFns` (`l2r_std_drop_workers` and its trampoline
  `l2r_std_drop_workers_c`, in programs that create tasks), `stdStreamFns`,
  `stderrPutFn`.
- **Remove only if:** never.

### Effect points and polling points

- **What:** lean-runtime's `effect()` comes before every output to a
  stream or file, a flush, a process spawn, `IO.Process.exit` and a panic
  message on the process's stderr (`io::stream_put`, `stream_flush`,
  `fs.rs`, `proc.rs`, `l2r_process_exit`, `panic_text`, `lean_panic`);
  its `poll()` at the program's clock reads (`IO.monoMsNow`,
  `IO.monoNanosNow`, `Std.Time.Timestamp.now`: `io::mono_nanos_polled`,
  `realtime_nanos_polled`), and, in a program that creates tasks, every
  1000th `ST.Ref` read (`ref_read`; next entry); `IO.getTaskState` and
  `IO.checkCanceled` poll by themselves. Before them, what natively would
  have run by then on other threads goes first (lean-runtime's rules: a
  sleep that is over, a task queued 5 ms ago, the event loop's due timers
  and ready descriptors).
- **Why:** lean-runtime's glue item 5.
- **Where:** `io.rs`, `fs.rs`, `proc.rs`, `lib.rs`, `refs.rs`;
  `runtime/prelude.rr`: `l2r_process_exit`, `l2r_io_mono_*`,
  `l2r_shim_realtime_nanos_i64`, `l2r_ref_*_point`.
- **Remove only if:** the runtime gets real threads.

### References in a program that creates tasks: polling, publication, and Lean 4.35's `modify`

- **What:** lean2rr decides at translation time whether the program
  creates tasks (`programCreatesTasks`): whether one of its extern
  instances, after the shim's replacements and with Lean's library's code
  it reaches, is `Task.spawn`, `Task.map`, `Task.bind`, `IO.asTask`,
  `IO.mapTask`, `IO.bindTask` or `IO.Promise.new` (all polymorphic, so
  each one reached is an instance). Every context other than `main`'s comes
  from these: tasks, a promise's dependents, and the event loop's
  completions, which resolve the promises the shim's Lean code makes; a
  `Std.Sync` object or a timer alone makes none. Only then does each reference
  operation get a point before its cell operation (`refPoint`; prelude
  `l2r_ref_*`; `refs.rs`):
  - `get`: a polling point (lean-runtime's `ref_read`: every 1000th read
    polls, once the first task started the scheduler);
  - `set`: a publication (`before_publish`);
  - `swap`: both; `take` (`modify`'s first half): both, and the reference
    is recorded as taken by the running frame (lean-runtime's keyed form
    of its rule, `sched::ref_keyed`, core 3.2, under the record's address:
    the context, the number of tasks running on it, and the innermost
    one);
  - while some reference is taken (one thread-local load), every other
    operation on it waits (`block_sync`) for the closing store, which
    wakes the waiters in the order they began to wait. The closing store
    is a `set` or `swap` in the frame that took it: modify's own store
    (lean2rr's option B: found at run time, so the generated code is
    unchanged). The taker's own `get` and `take` wait too: natively the
    reference is multi-threaded there and its `get` spins until modify's
    store, which never comes, so the program hangs (review RS4-01, test
    `RtRefOwnGetDuringModify`; before switch step 6 they read the
    placeholder, a value the program never stored). A store from code
    nested inside `modify`'s function (the `sync` dependent of a promise
    the function drops) waits, as in Lean 4.35; natively 4.34 stores into
    the empty slot and modify's store overwrites it (LB-01, not
    reproduced).
  Otherwise the reference operations are plain cell operations. A
  constant's walk for tasks reads a reference's cell directly
  (`refCellOpPlain`), as `lean_mark_persistent` does.
- **Why:** Owner's sign-off (option B, 2026-10-04): in a program with
  tasks these are correctness, not speed. Without the polling point a loop
  that polls a reference set by a task never ends (test `RtRefPollLoop`);
  without the wait a reference's `get`, `set` and `swap` see or overwrite
  the empty reference while `modify`'s function blocks (lean-runtime's
  glue item 7, Lean 4.35's rule; LB-01 and LB-18 not reproduced; tests
  `RtRefGetDuringModify`, `RtRefSetDuringModify`, `RtRefSwapDuringModify`,
  lean-runtime's `refs/*` cases). A program without them has one context,
  so it pays nothing: its generated code is unchanged. The decision is
  conservative: a task can only come from those externs, and the
  `Std.Sync` and event-loop primitives count although they need no task.
  The cost in task programs (a load and a branch per read and per write,
  a recorded `take` per `modify`) waits for an owner-approved timing
  session.
- **Where:** `lean2rr/LeanToReussir/Lower/Externs.lean`:
  `programCreatesTasks`, `refPoint`, `refCellOp`, `refCellOpPlain`;
  `Emit/Program.lean`: `lowerProgram`; `runtime/prelude.rr`:
  `l2r_ref_read_point`, `l2r_ref_write_point`, `l2r_ref_swap_point`,
  `l2r_ref_wait`, `l2r_ref_take_mark`; `runtime/leanrt/src/refs.rs`;
  lean-runtime's `sched::ref_keyed`.
- **Remove only if:** the runtime gets real threads (then the 4.35 rule
  stays, with atomics).

### lean-runtime's scheduler starts at the first task

- **What:** `main`'s start (`task::start`, Lean's `lean_init_task_manager`)
  is lean-runtime's lazy start (`sched::start_lazy`, audit item 4.5, since
  switch step 7): it only reads the task manager's number of workers
  (`LEAN_NUM_THREADS`, else the online processors) and the contexts' stack
  size, and answers `deferring` from them. lean-runtime builds the
  scheduler with lean2rr's glue at the first task, promise, `Std.Sync`
  object or operation, timer, signal watcher or socket: its own entry
  points for those call `ensure_started` (`spawn`, `depend`,
  `dependent_runs_now`, `promise_new`, every method of `sync`'s objects,
  `uv::loop_configure` and `loop_alive`, `Timer::new`, `Signal::new`,
  `TcpSocket::new`, `UdpSocket::new`, `dns::get_addr_info` and
  `get_name_info`), and the start turns reference reads into polling
  points. leanrt calls none of it itself. Until then a constant's claim and
  its store (lean-runtime's `step_keyed` and `done_keyed`,
  `once::claim_cold`, `set_raw`) take `main`'s context without building the
  scheduler's state (lean-runtime's fixes-6, asked for in switch step 6:
  before it, every program built that state, and read std's random hash
  keys, at its first constant), and the final run, `finish`, builds nothing
  either (the handed-off streams' writers, then the io layer's dedicated
  tasks: `task::shutdown`). The state is the thread's own (thread-locals),
  so `task::start`, `main` and `task::shutdown` all run inside the body
  that `rt::run_main2` gives `io::startup::run_main`, on `main`'s thread;
  during the initializers nothing is started.
- **Why:** A program that creates no tasks pays nothing for the scheduler
  (owner's rule, as for C externs): no scheduler state, contexts or event
  loop are built, nor their code paged in; until a task exists nothing
  could have been deferred or run elsewhere, so the two are the same. The
  number of workers is still read at `main`'s start: the same system calls
  as natively. The lazy start was leanrt's own (its `ensure_started`,
  `start_sched` and the flags beside them) until switch step 7 moved it
  into the crate.
- **Where:** `task.rs`: `start`, `deferring`, `shutdown`; `sched.rs`:
  `LeanrtGlue`; `once.rs`: `claim_cold`; lean-runtime's `src/sched/mod.rs`
  (`start_lazy`, `ensure_started`, `deferring`).
- **Remove only if:** never (the owner's rule: a program without tasks
  pays nothing for the scheduler).

### A stream handle's drop runs in lean-runtime's no-suspend scope

- **What:** The drop of a stream handle (`fs::FileHandle`, in or out of a
  free) runs inside `sched::no_suspend()`: there a dropped stream's flush
  never waits (it
  writes what the descriptor takes and hands the rest to a writer thread
  of lean-runtime's), and the io layer's other waits block the thread.
  The writers are waited for at the context's next point that publishes:
  a cell store (`l2r_lcell_set`), a task's or `main`'s end, every
  scheduler call; `IO.Process.forceExit` waits for them before `_exit`
  (`io::force_exit`).
- **Why:** lean-runtime's glue item 11 asks for its no-suspend scope over
  the whole free path: lean2rr's runtime must never suspend inside a free
  (review RSIO-03), and a pipe whose reader is a task of the same program
  must still get every byte (RSIO-09). lean2rr enters the scope at the one
  step of a free that can wait, the handle's drop; nothing else a free
  reaches waits (a promise it drops is resolved after the free, its cell's
  store included, since switch step 6: [dependents.md](dependents.md);
  before, that store ran in the scope too: review RS4-04, test
  `RtPromiseDropInFreeWait`; a task's release never waits), so the free
  path itself (`drop::run`, on every free) stays without the scope's cost.
- **Where:** `fs.rs`: `close`, `close_deferred`; `io.rs`: `force_exit`;
  `drop.rs`: `run`.
- **Remove only if:** never.

### The event loop is lean-runtime's: timers, signals and sockets complete through promises

- **What:** Timers and signal watchers are lean-runtime's
  (`sched::uv::Timer`, `Signal`), sockets and name resolution its `net`,
  all on its scheduler's event loop (one per program: epoll, its timers and
  watches; the loop's callbacks run on a loop context of their own). The
  shim (`lean2rr/L2RShim.lean`) makes the program's promise `p` and a
  promise `r` of `Unit` whose `sync` continuation resolves `p` from the
  operation's outcome (`Op`); lean-runtime's completion closure
  (`net::Completion`; for a timer or watcher the loop's promise,
  `net::LoopP`) stores the outcome and drops its reference to `r`, so the
  continuation runs on the loop context, as libuv's callback runs on
  libuv's thread. An operation lean-runtime gives up (its closure dropped
  uncalled: `cancelRecv`, `cancelAccept`, a stopped timer) is marked
  canceled, and the continuation does nothing.
- **Why:** The runtime cannot build Lean values, and no generated code may
  run inside a runtime primitive (5021ddf, 470425c); one event loop per
  program (switch step 4: leanrt's own loop, `net.rs`'s reactor, is gone).
- **Where:** `net.rs`: `Completion`, `LoopP`, `next_op`, `pending`;
  `lean2rr/L2RShim.lean`: `whenDone`, `completion`. See
  [../externs-ffi/shim.md](../externs-ffi/shim.md).
- **Remove only if:** never.

### Stack overflow is reported as Lean does, on every stack

- **What:** lean-runtime's `sched::install_stack_overflow_handler()`
  (feature `stack-overflow`) on each thread that runs Lean code, at its
  entry: the process's main thread before the initializers and `main`'s
  thread (`rt::run_main2`, at the start of the body it gives
  `io::startup::run_main`; the scheduler's start registers `main`'s thread
  again). A fault in the guard page of the thread's stack, or of
  the running context's, prints `Stack overflow detected. Aborting.` and
  aborts (status 134, stdout not flushed); another fault takes the
  default action.
- **Why:** As Lean's `stack_overflow.cpp`; lean-runtime's glue item 8.
  leanrt's own handler is gone (it also took a fault below the stack with
  the stack pointer below it, a frame skipping the guard page, b1cd76c;
  `RtStackOverflow`'s GMP case passes with lean-runtime's).
- **Where:** `rt.rs`: `install_stack_overflow_handler`, `run_main2`;
  lean-runtime's `src/sched/stack_overflow.rs`.
- **Remove only if:** never.

### `Std.Sync` is lean-runtime's

- **What:** `BaseMutex`, `Condvar`, `BaseRecursiveMutex` and
  `BaseSharedMutex` are lean-runtime's (`sched::sync`) in runtime handles:
  locks belong to threads (a context, and on it the innermost running
  task's thread), glibc's and libc++'s rules, waits that let the others go
  on. Each of lean-runtime's methods, the constructors included, starts
  the scheduler first if the lazy start is waiting for it (its
  `ensure_started`; until switch step 7 leanrt's `settle` did it before
  each call), and promises resolved inside a free are resolved in
  lean-runtime.
- **Why:** As Lean's `mutex.cpp` over `std::mutex` & co. (f87ea08); one
  implementation (lean-runtime's, from leanrt's). A lock's owner is a
  thread, which lean-runtime tells apart from an initializer's by its
  scheduler having started: with the scheduler started only at the first
  task, a mutex an initializer made, locked by `main` before that task and
  again (nested) after it, had two owners, and `main` waited for itself
  forever (review RS4-05, test `RtRecMutexLazyStart`). The owner names
  the OS thread (lean-runtime's AR-39, fixed in 471f458, fixes-7; review
  RS7-02): until then it told an initializer from `main` by the scheduler
  having started, so a lock an initializer kept, taken again by `main`,
  hung with `LEAN_MAIN_USE_THREAD=0` (natively nested on one thread) and
  was taken with `LEAN_NUM_THREADS=0` on `main`'s own thread (natively a
  deadlock; now `main` waits forever too, the hub asleep, nothing printed);
  test `RtRecMutexInitOwner`.
- **Where:** `sync.rs`; lean-runtime's `src/sched/sync.rs`.
- **Remove only if:** never.
