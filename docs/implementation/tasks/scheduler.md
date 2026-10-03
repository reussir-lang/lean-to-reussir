# The scheduler

A thread that blocks natively (a lock, a condition variable, a task or
promise not finished yet, a sleep, a socket) lets others go on. The runtime
reproduces that on one thread with *contexts*. Paths: `runtime/leanrt/src/`
unless they say otherwise. Plan
[§5.14](../../translation-plan.md#514-thunks-and-tasks) ("Blocking").

### Contexts are stacks of their own on one thread

- **What:** `main`'s context runs on its thread's stack; each task the
  scheduler starts gets a stack of a native worker's size (1 GiB, or
  `LEAN_STACK_SIZE_KB`), reserved without committing memory
  (`MAP_NORESERVE`), with a guard page. A switch saves the callee-saved
  registers on the stack and swaps stack pointers (aarch64 and x86-64
  assembly), and saves and restores the per-context state: running tasks,
  walks and chains (`task::CtxState`), and the mutable cells with the
  current standard streams (`once::CtxState`). A task that is *needed*
  still runs nested, on the stack of whoever needs it.
- **Why:** A task nested on its caller's stack makes everything below it
  wait for it; a context can be suspended and resumed instead (f87ea08).
  Reussir's LLVM coroutine bindings were not used: tasks need stackful
  contexts.
- **Where:** `coro.rs`: `switch`, `set_running`, `in_guard`,
  `within_stack`, `past_end`; `sched.rs`: `switch_to`, `block`,
  `yield_now`, `wake`, `start_worker`, `free_zombie`;
  `task.rs`: `swap_ctx_state`; `once.rs`: `swap_ctx_state`.
- **Remove only if:** the runtime gets real threads.

### What runs when the running context blocks

- **What:** The scheduler runs, in this order: a suspended context that
  can go on (in the order they became able to); else a queued task on a
  new context, if one of the task manager's workers is free (a context
  running a task holds one, except while it waits for a task or promise;
  a dedicated task always starts); else the event loop's timers and
  sockets and the sleepers, waiting for the first of them. When nothing
  can ever go on, the program waits forever, as a deadlocked native one
  does.
- **Why:** As native threads within Lean's number of workers.
- **Where:** `sched.rs`: `schedule`, `block`, `sleep`, `workers_alive`;
  `task.rs`: `startable`, `holds_worker`, `pool_in_use`.
- **Remove only if:** the runtime gets real threads.

### Effect points let what is due run first

- **What:** Output to a stream or file, flushing a handle, spawning a
  process and `IO.Process.exit` are effect points: before them, what
  natively would have run by then on other threads goes first: a context
  whose sleep is over, a due timer and what its completion releases, ready
  descriptors and signals, a context able to run for 5 ms (a lock handed
  over, a promise resolved), a task queued 5 ms ago with a worker free;
  then, round after round (up to 64), what those release. What runs in
  those rounds starts no tasks at its own effect points. `IO.sleep 0` does
  one such round without the 5 ms ages: due sleepers and timers, ready
  descriptors, every context able to run, and a task queued at least a
  worker's wake-up time (90 µs) ago.
- **Why:** Sleeps and timers then order the output of tasks by time, as
  natively, as long as code between two outputs is shorter than the sleeps
  (7edc0f5, 6f14a9e). A context otherwise never loses the processor.
- **Where:** `sched.rs`: `effect`, `effect_slow`, `STALE`, `zero_sleep`,
  `sleeper_due`; `task.rs`: `stale_startable`, `WORKER_LATENCY`; `io.rs`, `fs.rs`, `proc.rs` (the calls to
  `sched::effect`); `runtime/prelude.rr`: `l2r_process_exit`.
- **Remove only if:** the runtime gets real threads.

### Effect points poll the event loop at most every 50 µs

- **What:** An effect point polls the descriptors and signals the event
  loop watches only if 50 µs have passed since its last poll; sleeps,
  `IO.sleep 0` and polling loops still poll every time.
- **Why:** With an `accept` pending, every output line made a `poll(2)`
  call: an output loop cost 4-6x native CPU (100002 `ppoll` calls for
  100000 lines; 522 after). 50 µs is within a native thread's wake-up
  latency (round 7 RV7C-06, 65996c4; test `RtNetEffectPoll`).
- **Where:** `sched.rs`: `poll_due`, `POLL_EVERY`, `effect_slow`;
  `net.rs`: `poll_now`.
- **Remove only if:** never.

### The event loop completes operations through promises

- **What:** An operation that completes later (a timer, data received, a
  connection accepted) gets from the shim a promise `r` of `Unit` with a
  `sync` continuation that resolves the program's promise. When the
  operation completes, the runtime stores the outcome in its `Op` and drops
  `r` on the event loop's own context, which resolves it with `none` and
  runs the continuation there, as libuv's callback runs on libuv's thread.
  A promise the loop gives up without resolving it is released on the
  loop's context too, at its next turn. The scheduler polls descriptors and
  timers when nothing else can go on, and fires a due timer at the next
  effect point.
- **Why:** The runtime cannot build Lean values, and no generated code may
  run inside a runtime primitive (5021ddf, 470425c).
- **Where:** `net.rs`: `release`, `deliver`, `wait`, `process_due`,
  `fire`; `sched.rs`: `ensure_evloop`, `wake_evloop`;
  `lean2rr/L2RShim.lean`: `whenDone`. See
  [../externs-ffi/shim.md](../externs-ffi/shim.md).
- **Remove only if:** never.

### No busy wait while the event loop's context is blocked

- **What:** `wake_evloop` answers whether it woke the event loop's
  context; `net::wait` returns early only then. Otherwise completions wait
  for the context and `net::wait` waits for timers, sockets and the
  earliest sleeper as usual.
- **Why:** When the loop's context was blocked inside a `sync`
  continuation (natively a libuv callback that blocks, e.g. a dependent
  that sleeps) and another completion arrived, the scheduler looped back
  into `net::wait` without waiting: 100% CPU (round 7 RV7C-07, 370226e;
  test `RtTimerSyncSleep`).
- **Where:** `sched.rs`: `wake_evloop`; `net.rs`: `wait`.
- **Remove only if:** never.

### Signal watchers use the loop's signal pipe opened at startup

- **What:** The signal handler writes to the non-blocking pipe the
  runtime opened at startup in the place libuv's loop opens its signal
  pipe (`rt::signal_pipe`); `net::wait` watches it. A new pipe is made only
  if that one could not be opened. Stopping the last watcher of a signal
  restores its default action, as libuv does.
- **Why:** The first watcher used to make a new self-pipe: two
  descriptors native Lean does not open, so later descriptors were
  numbered two higher and `EMFILE` came two opens earlier (round 7
  RV7C-05, 10b7568; test `RtSignalFd`).
- **Where:** `rt.rs`: `signal_pipe`, `reserve_libuv_descriptors`;
  `net.rs`: `signal_start`, `signal_stop`, `read_signals`, `wait`.
  Startup descriptors:
  [../startup/entry.md](../startup/entry.md#native-leans-startup-descriptors-are-opened-by-an-elf-constructor).
- **Remove only if:** never.

### Stack overflow is reported as Lean does, on every stack

- **What:** Every thread that runs Lean code installs a SIGSEGV/SIGBUS
  handler on an alternate signal stack (mmapped with a guard page). A fault
  in the guard page of the thread's stack or of the running context's
  stack, or a fault below the stack while the stack pointer is below it,
  prints `Stack overflow detected. Aborting.` and aborts (status 134,
  stdout not flushed). The scheduler records the running context's stack
  at each switch and at a new context's entry.
- **Why:** As Lean's `stack_overflow.cpp`. The guard page was one global,
  overwritten by each thread (b1cd76c); a frame without stack probes (GMP's
  scratch space) skips the guard page (b1cd76c); contexts were found
  through a fixed table of 4096 stacks, so an overflow past 4096 live
  contexts was a plain SIGSEGV (round 7 RV7C-04, 1eaea77; test
  `RtStackOverflowContexts`).
- **Where:** `rt.rs`: `install_stack_overflow_handler`, `segv_handler`,
  `current_stack_guard`, `interrupted_sp`, `OVERFLOW_SP_REACH`;
  `coro.rs`: `set_running`, `in_guard`, `past_end`; `sched.rs`:
  `note_running_stack`.
- **Remove only if:** never.

### Each task starts with the process's standard streams

- **What:** A task run as on a worker thread starts with empty stream
  cells (rebuilt as the process's streams on first use) and puts the
  runner's cells back when it ends (`l2r_std_enter_if`/`l2r_std_leave_if`
  over `once::push_context`/`pop_context`); a task run on the current
  thread (a `sync` dependent, priority 2^32-1) shares that thread's
  streams. Panics, `dbgTrace` and `timeit` write through the current
  stderr stream (`l2r_stderr_put`).
- **Why:** Natively `IO.setStdout` & co. replace the current thread's
  streams, and a task runs on a worker thread (adv2 EFF-1, f9e06af). The
  translation behaves as if every task had a fresh worker (plan
  [§10](../../translation-plan.md#10-known-divergences-and-unsupported-features)).
- **Where:** `lean2rr/LeanToReussir/Lower/Externs.lean`: `stdContextFns`,
  `stdStreamFns`, `stderrPutFn`; `Lower/LazyForce.lean`: `lazyGetFn`;
  `once.rs`: `push_context`, `pop_context`.
- **Remove only if:** never.

### Locks belong to threads, with glibc's and libc++'s rules

- **What:** `Std.Sync`'s `BaseMutex`, `Condvar`, `BaseRecursiveMutex` and
  `BaseSharedMutex` are runtime handles. A lock's owner is a thread: a
  context and, on it, the innermost running task (a task needed by another
  runs on a worker thread natively). Waiting blocks the context. As glibc,
  relocking a held `BaseMutex` waits forever, `tryLock` fails, and a
  released mutex goes to the longest waiter; the shared mutex follows
  libc++ (an entered writer keeps new readers out).
- **Why:** As Lean's `mutex.cpp` over `std::mutex` & co. (f87ea08).
- **Where:** `sync.rs`: `mutex_lock`, `condvar_wait`, `recmutex_lock`,
  `sharedmutex_write`, `settle`, `me`.
- **Remove only if:** never.
