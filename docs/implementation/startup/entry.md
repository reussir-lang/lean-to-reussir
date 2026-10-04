# The entry point

The generated `#[main]` does what Lean's generated `main` does. Paths:
`lean2rr/LeanToReussir/` for lean2rr's files, `runtime/` for the runtime.
Plan [§5.11](../../translation-plan.md#511-program-entry).

### Initializers on the main thread, `main` on a 1 GiB thread

- **What:** `leanrt::rt::run_main2` runs the startup chain
  (`l2r_init_body`, which sets `IO.initializing` and clears it at the end)
  on the process's main thread (8 MiB stack), then `l2r_main_body` (which
  starts the task manager, then calls `main`) on a new thread with a
  1 GiB stack (`LEAN_STACK_SIZE_KB`); with `LEAN_MAIN_USE_THREAD=0`, on
  the main thread instead.
- **Why:** As native Lean: a deep initializer overflows natively at
  8 MiB, and deep non-tail recursion in `main` is common (runtime requests
  13, 23, 24; be9f201).
- **Where:** `Emit/Entry.lean`: `lowerEntry`; `Emit/Startup.lean`:
  `startupChain`; `runtime/leanrt/src/rt.rs`: `run_main2`, `run_body`,
  `set_initializing`, `main_on_thread`.
- **Remove only if:** never.

### `main` gets fresh standard streams only on a thread of its own

- **What:** The entry enters a fresh standard-stream context for `main`
  (`l2r_std_enter_if`) only when `main` runs on its own thread; with
  `LEAN_MAIN_USE_THREAD=0` it keeps the streams the initializers left.
- **Why:** Natively a new thread starts with the process's streams, while
  the initializers' thread keeps an `IO.setStdout` an `initialize` made
  (round 7 RV7O-03, 28163ad; test `RtInitRedirectNoThread`).
- **Where:** `Emit/Entry.lean`: `lowerEntry`; `Lower/Externs.lean`:
  `stdContextFns`; `runtime/leanrt/src/rt.rs`: `main_on_thread`.
- **Remove only if:** never.

### Pending tasks run after `main`, before the exit status

- **What:** After `main` returns, whatever its result, the entry sets
  Lean's shutdown flag and runs the tasks still pending
  (`l2r_task_shutdown`, `l2r_run_pending_tasks`); then it reports an
  uncaught exception (`uncaught exception: <message>`, exit 1) or exits
  with the returned `UInt32` (0 for `IO Unit`).
- **Why:** `lean_finalize_task_manager` waits for the tasks before the
  result is looked at.
- **Where:** `Emit/Entry.lean`: `lowerEntry`; `Lower/Promises.lean`:
  `taskDispatchFns`. See [../tasks/deferral.md](../tasks/deferral.md).
- **Remove only if:** never.

### `main`'s argument list reads `argv` once

- **What:** `main`'s `List String` is built by a generated loop from the
  last argument, over `argv` read once and kept (`leanrt::rt::args`).
- **Why:** Reading `argv` per argument was quadratic (round 6, 1362da1).
- **Where:** `Emit/Entry.lean`: `lowerEntry` (`l2r_mk_args`);
  `runtime/prelude.rr`: `l2r_argv`, `l2r_argc`;
  `runtime/leanrt/src/rt.rs`: `args`.
- **Remove only if:** never.

### Native Lean's startup descriptors are opened by an ELF constructor

- **What:** Before Rust's runtime starts, an `.init_array` constructor
  has lean-runtime open the descriptors native Lean's libuv loop has open
  at startup (`io::startup::open_native_descriptors`: epoll, two io_uring
  rings when libuv would make them, mapped as libuv maps them, the signal
  lock pipe with its byte, the loop's signal pipe, an eventfd),
  close-on-exec, in that order, at the lowest free numbers. A standard
  descriptor closed at startup is taken by the first of them, as natively.
  When they cannot be made, the program ends there with lean-runtime's
  `INTERNAL PANIC: Failed to initialize event loop: ...` (`fail_as_native`;
  LB-30, LB-31). Signal watchers use the loop's signal pipe, which
  `rt::signal_pipe` claims from lean-runtime
  (`io::startup::claim_signal_pipe`, AR-17). The constructor is in the
  plain `.init_array` section, so it runs after the prioritized ones:
  Rust std's (`.init_array.00099`, the arguments) and lean-runtime's
  `proc-title` constructor (`.init_array.00100`, AR-20), which keeps the
  arguments' memory before any startup descriptor exists, as native's
  `lean_setup_args` runs before libuv's loop (review RST3-01: after it, at
  one free descriptor the title could not be written).
- **Why:** `/proc/self/fd`, the numbers of the descriptors the program
  opens and the point where opening fails with `EMFILE` are then native's
  (84a4c08, test `RtFdLimit`). Running before Rust's runtime also keeps it
  from putting `/dev/null` in the place of closed standard descriptors,
  which could not be told apart later from a `/dev/null` the program was
  given (a94fafd). Watchers made a new pipe of their own, two descriptors
  native Lean does not open (round 7 RV7C-05, 10b7568). lean-runtime has
  no constructor of its own for them (its glue duty, `io::startup`); its
  rings are real and made only when libuv would make them, so
  `RtFdStartupNoUring` passes (switch step 3).
- **Where:** `runtime/leanrt/src/rt.rs`: `startup_descriptors`,
  `open_startup_descriptors`, `reserve_native_descriptors`,
  `signal_pipe`, `is_rust_dev_null`; lean-runtime's `src/io/startup.rs`.
- **Remove only if:** never.

### Exit finishes the streams as a native program does

- **What:** At exit (also `IO.Process.exit` and internal panics), stdout
  is flushed first, then the pending output of every `FILE` newest first,
  then used buffered streams are synced (a seekable stdin is left where the
  program stopped reading): lean-runtime's `io::exit::exit`, which every
  normal end of the process calls (`leanrt::io::exit`). `main`'s return
  (`l2r_exit`, `io::main_exit`) and an uncaught error first wait for
  lean-runtime's dedicated tasks (`io::exit::after_main`), as
  `lean_finalize_task_manager` does.
- **Why:** libc++'s `ios_base::Init` destructor, then glibc's
  `_IO_cleanup`: the bytes and their order on the descriptors match
  (d2ae23d).
- **Where:** `runtime/leanrt/src/io.rs`: `exit`, `main_exit`;
  `runtime/leanrt/src/lib.rs`: `uncaught_exception`; lean-runtime's
  `src/io/exit.rs`; `runtime/prelude.rr`: `l2r_exit`.
- **Remove only if:** never.

### The program exports C trampolines the runtime calls back

- **What:** Every program defines `extern "C"` trampolines:
  `l2r_init_body`, `l2r_main_body`, `l2r_stderr_put_c` (the runtime's own
  diagnostics), `l2r_task_run_one_c` and `l2r_task_walk_c` (the
  scheduler); programs that create promises also define
  `l2r_promise_drop_c` (a promise's last release). The runtime links some
  of them weakly.
- **Why:** The runtime cannot name generated code; calling through Rust
  also removes a Reussir-level call cycle through the stream code that
  crashed rrc ([Reussir bug 5](../../../reussir-bugs/05-one-armed-if.md)).
- **Where:** `Emit/Entry.lean`: `lowerEntry`; `Lower/Promises.lean`:
  `promiseResolveFn`, `taskDispatchFns`; `runtime/leanrt/src/io.rs`:
  `diag_put`.
- **Remove only if:** never.
