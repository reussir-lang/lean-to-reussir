# The entry point

The generated `#[main]` does what Lean's generated `main` does. Paths:
`lean2rr/LeanToReussir/` for lean2rr's files, `runtime/` for the runtime.
Plan [§5.11](../../translation-plan.md#511-program-entry).

### Initializers on the main thread, `main` on a 1 GiB thread

- **What:** `leanrt::rt::run_main2` runs the startup chain
  (`l2r_init_body`, which sets `IO.initializing` and clears it at the end)
  on the process's main thread (8 MiB stack), then `l2r_main_body` (which
  starts the task manager, calls `main`, then runs the final run of tasks)
  through lean-runtime's `io::startup::run_main` (audit item 4.2, since
  switch step 7): on a new thread with a 1 GiB stack
  (`sched::thread_stack_size`, `LEAN_STACK_SIZE_KB`), or with
  `LEAN_MAIN_USE_THREAD=0` (exactly `0`) on the main thread instead. The
  body first installs Lean's stack-overflow report. The thread has no name
  of its own: it keeps the process's (`/proc/thread-self/comm`), as
  native's `lthread`. A Rust panic (a runtime bug) inside the generated
  code (`l2r_main_body` and every frame below it, the runtime's textures
  included) cannot unwind: Rust reports "panic in a function that cannot
  unwind" and aborts (status 134, buffered stdout lost), in both modes;
  only a panic in the glue's own frames (`run_main2`'s closure,
  `install_stack_overflow_handler`) comes back from `run_main` as `Err`,
  and the process exits with status 101, its streams written.
- **Why:** As native Lean: a deep initializer overflows natively at
  8 MiB, and deep non-tail recursion in `main` is common (runtime requests
  13, 23, 24; be9f201). The thread is lean-runtime's since switch step 7
  (leanrt's own `run_body` named it `main`: a Rust panic's header said
  `thread 'main'` there, now `thread '<unnamed>'`). What a panic does is
  unchanged from before step 7 (review RS7-01: a panic inside the
  generated code aborted with status 134 in both modes then too). The task manager's
  start, `main` and the final run all run inside the body, since the
  scheduler's state is the thread's own (lean-runtime's review RSH2-03).
- **Where:** `Emit/Entry.lean`: `lowerEntry`; `Emit/Startup.lean`:
  `startupChain`; `runtime/leanrt/src/rt.rs`: `run_main2`,
  `set_initializing`, `main_on_thread`; lean-runtime's
  `src/io/startup.rs`: `run_main`, `main_on_thread`.
- **Remove only if:** never.

### `main`'s thread allocates on transparent huge pages

- **What:** Nothing allocates before mimalloc's own constructor has run:
  lean-runtime's ELF constructors (`proc-title`'s, `.init_array.00100`,
  and `startup-fds`'s, `.init_array.00101`) use no global allocator (its
  audit item AR-36, checked by its `tests/ctor_alloc.rs`). So the process's
  main thread reserves mimalloc's first arena (1 GiB) with large OS pages,
  and the segments of `main`'s thread come from it: the heap is on
  transparent huge pages, as native Lean's mimalloc v3 advises every
  arena. leanrt sets no mimalloc option for this (its one option is the
  next entry's).
- **Why:** From switch step 3 to step 6, lean-runtime's argument
  constructor allocated before mimalloc's constructor, so mimalloc gave
  the main thread a 32 MiB segment from the OS and reserved no arena. The
  first arena was then reserved for the first segment of `main`'s thread,
  which mimalloc v2 delays (`eager_commit_delay` 1) and so does not let use
  large OS pages: it had no `MADV_HUGEPAGE`, and with transparent huge
  pages in `madvise` mode the heap's first GiB took one page fault per
  4 KiB (`deriv` at size 11: 263,000 faults, native 2,800). dev eb0ea40
  worked around it (`alloc::heap_on_huge_pages`: `eager_commit_delay` at 0
  before `main`'s thread started). With AR-36 (switch step 7) the
  workaround changed nothing measured, and was removed: `deriv` at size 11
  1,920 faults with it, 1,922 without (dev 698e92b without it: 263,329);
  `rbtree-ck` at 4,200,000 704 and 705 (dev without it: 262,152); `Qsort`
  at 80 133 and 134; peak RSS the same (`Qsort` at 80: 7,140 and 7,144 KB;
  `deriv` at 11: 3,650,692 and 3,650,756 KB). Measured with
  `MIMALLOC_EAGER_COMMIT_DELAY=1` (mimalloc v2's default), which the
  workaround left alone.
- **Where:** lean-runtime's `src/io/argv_title.rs` and
  `src/io/startup_fds.rs` (AR-36), `tests/ctor_alloc.rs`.
- **Remove only if:** this is a constraint, not code: an ELF constructor
  that allocates before mimalloc's own (one of lean-runtime's, Reussir's,
  or leanrt's) brings the page faults back; after adding one, check
  `deriv`'s page faults at size 11 (`/usr/bin/time -v`).

### Free arena memory goes back to the OS at once (mimalloc v2.1.8 to v2.2.7)

- **What:** The first call of `run_main2`, before the module initializers,
  is `alloc::purge_arenas_at_once`: when `mi_version()` is 218 to 227
  (mimalloc v2.1.8 to v2.2.7; Reussir's `libmimalloc-sys` 0.1.44 bundles
  v2.2.4) and the environment does not set `MIMALLOC_ARENA_PURGE_MULT` (in
  any case, as mimalloc reads its variables), it sets mimalloc's
  `arena_purge_mult` to 0 (`mi_option_set`, option 24 in the
  `include/mimalloc.h` of every version of the range). An arena then purges
  a free range (a whole 32 MiB segment, or the segment of a huge block of
  more than 16 MiB) when it is freed, instead of `purge_delay` x
  `arena_purge_mult` ms (10 x 10) later. Purges inside segments keep their
  10 ms delay; `MIMALLOC_PURGE_DELAY=-1` still turns purging off (the OS
  layer tests it). leanrt declares `mi_version` and `mi_option_set` itself
  and links them from Reussir's mimalloc, as its `mi_malloc`.
- **Why:** In these versions `mi_arenas_try_purge` (v2.2.4 `src/arena.c`,
  line 624: `if (!force && (arenas_expire == 0 || arenas_expire < now))
  return;`) returns when the purge time has passed, which is when it should
  purge, so the delayed arena purges run almost never and freed huge
  blocks and segments stay in the process until they are used again.
  v2.1.8 added the test; v2.3.0 fixed it (`> now`); v3 never had it
  (checked in each tag's `src/arena.c`). Measured on 16 benchmark
  programs with `MIMALLOC_ARENA_PURGE_MULT=0`: lean-zip's peak 422 to
  330 MiB (native 394 MiB), wall time +0.9 % (about 65 ms of system time);
  no other program's peak changed, the other wall times within noise. With
  this function itself (dev 604b97e4): lean-zip 432,024 to 337,820 KB, the
  output unchanged. [Reussir issue 46](../../../reussir-bugs/46-mimalloc-arena-purge.md)
  (kind: issue (dependency); a newer `libmimalloc-sys` is parked). Test
  `RtArenaPurge` (`.alloc`: peak memory of `ByteArray`s made as huge
  blocks, grown and dropped: 56,400 KB with the option, 77,000 KB
  without); unit tests `alloc::tests::arena_purge_gate`,
  `alloc::tests::env_has_ignores_case`, `alloc::tests::arena_purge_mult_set`.
  `env_has` reads C's `environ` itself: `std::env::vars_os` copied every
  variable at every start (136 more allocations in the pay-nothing
  counts).
- **Where:** `runtime/leanrt/src/alloc.rs`: `purge_arenas_at_once`,
  `ARENA_PURGE_INVERTED`, `MI_OPTION_ARENA_PURGE_MULT`, `env_has`;
  `runtime/leanrt/src/rt.rs`: `run_main2`.
- **Remove only if:** Reussir's mimalloc is v2.3.0 or later (or v3): out
  of the range the function already does nothing, so then delete it, its
  call and its unit tests. `RtArenaPurge` stays; check its bounds with the
  new mimalloc, whose fixed arena purges still wait 100 ms after a free.

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

- **What:** After `main` returns, whatever its result, the entry calls
  `l2r_task_shutdown`: lean-runtime's `finish` sets Lean's shutdown flag,
  runs the tasks still pending and waits for them (and for the io layer's
  dedicated tasks); the generated final run (`l2r_run_pending_tasks`) then
  finds nothing. Then it reports an uncaught exception (`uncaught
  exception: <message>`, exit 1) or exits with the returned `UInt32` (0 for
  `IO Unit`).
- **Why:** `lean_finalize_task_manager` waits for the tasks before the
  result is looked at (lean-runtime's glue item 2; LB-13 not reproduced:
  a pool task enqueued after `main` still runs).
- **Where:** `Emit/Entry.lean`: `lowerEntry`; `runtime/leanrt/src/task.rs`:
  `shutdown`, `next_tag`; `Lower/Promises.lean`: `taskDispatchFns`. See
  [../tasks/deferral.md](../tasks/deferral.md).
- **Remove only if:** never.

### `main`'s argument list reads `argv` once

- **What:** `main`'s `List String` is built by a generated loop from the
  last argument, over `argv` read once and kept (`leanrt::rt::args`); each
  string is boxed into the list's head field (`List`'s one type holds a
  `Box`).
- **Why:** Reading `argv` per argument was quadratic (round 6, 1362da1).
- **Where:** `Emit/Entry.lean`: `lowerEntry` (`l2r_mk_args`, a generated
  function, not raw text, so that the head is boxed as everywhere else);
  `runtime/prelude.rr`: `l2r_argv`, `l2r_argc`;
  `runtime/leanrt/src/rt.rs`: `args`.
- **Remove only if:** never.

### The raw text of the entry point reads IO results through generated functions

- **What:** The entry point and the startup chain are raw text that
  matches IO results (`EST.Out`, one type, whose `ok` and `error` fields
  are `Box`es). They read the fields through generated functions: the
  exit code of a `main : IO UInt32` through `l2r_main_code` (unboxes the
  `UInt32`), an uncaught error's text through `l2r_err_string` (unboxes
  the `IO.Error`, then Lean's `IO.Error.toString`), and an `initialize`
  constant's value is stored into its once-cell at the constant's own
  type by `l2r_init_put_<slot>` (the type its reads take it at,
  `Callee.initConst`).
- **Why:** The text cannot box or unbox: it hard-coded the field types, so
  with `Box` fields the exit code was always 0 and the stored constant had
  another type than its reads.
- **Where:** `Emit/Entry.lean`: `lowerEntry`; `Emit/Startup.lean`:
  `ioResultOf` (the payload's own type too), `errStringFn`, `initPutFn`,
  `startupChain`.
- **Remove only if:** never.

### Native Lean's startup descriptors are opened by an ELF constructor

- **What:** Before Rust's runtime starts, lean-runtime's own ELF
  constructor (feature `startup-fds`, audit item 4.3, since switch step 7)
  opens the descriptors native Lean's libuv loop has open at startup
  (`io::startup::open_native_descriptors`: epoll, two io_uring rings when
  libuv would make them, mapped as libuv maps them, the signal lock pipe
  with its byte, the loop's signal pipe, an eventfd), close-on-exec, in
  that order, at the lowest free numbers. A standard descriptor closed at
  startup is taken by the first of them, as natively. When they cannot be
  made, the program ends there with lean-runtime's `INTERNAL PANIC: Failed
  to initialize event loop: ...` and status 1 (LB-30, LB-31). Signal
  watchers use the loop's signal pipe and the scheduler's event loop the
  epoll descriptor (lean-runtime's `sched` takes them from `io::startup`).
  The constructor is in `.init_array.00101`, so it runs after Rust std's
  (`.init_array.00099`, the arguments) and lean-runtime's `proc-title`
  constructor (`.init_array.00100`, AR-20), which keeps the arguments'
  memory before any startup descriptor exists, as native's
  `lean_setup_args` runs before libuv's loop (review RST3-01: after it, at
  one free descriptor the title could not be written). It acts only in the
  program's own executable and uses no global allocator (AR-36). At
  `main`'s start `rt::run_main2` calls
  `io::startup::ensure_native_descriptors()`, which keeps the constructor
  linked and, if it did not act (under `ld.so ./prog` or without `/proc`:
  lean-runtime's accepted deviations RSH2-11), opens them where they
  land; it closes nothing, so a standard descriptor closed at startup
  then stays Rust's `/dev/null`.
- **Why:** `/proc/self/fd`, the numbers of the descriptors the program
  opens and the point where opening fails with `EMFILE` are then native's
  (84a4c08, test `RtFdLimit`). Running before Rust's runtime also keeps it
  from putting `/dev/null` in the place of closed standard descriptors,
  which could not be told apart later from a `/dev/null` the program was
  given (a94fafd). Watchers made a new pipe of their own, two descriptors
  native Lean does not open (round 7 RV7C-05, 10b7568). The rings are
  real and made only when libuv would make them, so `RtFdStartupNoUring`
  passes (switch step 3). Until switch step 7 the constructor was
  leanrt's (`rt.rs`, plain `.init_array`), with a fallback that closed the
  read-write `/dev/null`s on descriptors 0 to 2 when it had not run;
  lean-runtime keeps no such recovery (a safe function that closes
  descriptors it does not own: its reviews RSH2-04, LS2-01).
- **Where:** `runtime/leanrt/src/rt.rs`: `run_main2`; `scripts/l2r.py`:
  `LEAN_RUNTIME_BASE_FEATURES` (`startup-fds`); lean-runtime's
  `src/io/startup.rs` and `src/io/startup_fds.rs`.
- **Remove only if:** never.

### Exit finishes the streams as a native program does

- **What:** At exit (also `IO.Process.exit` and internal panics), stdout
  is flushed first, then the pending output of every `FILE` newest first,
  then used buffered streams are synced (a seekable stdin is left where the
  program stopped reading): lean-runtime's `io::exit::exit`, which every
  normal end of the process calls (`leanrt::io::exit`; for
  `IO.Process.exit`, the internal panics, the panics that end the process
  and an uncaught error, lean-runtime's `io::panic` since switch step 8).
  `main`'s return (`l2r_exit`, `io::main_exit`) and an uncaught error
  first wait for lean-runtime's dedicated tasks (`io::exit::after_main`),
  as `lean_finalize_task_manager` does.
- **Why:** libc++'s `ios_base::Init` destructor, then glibc's
  `_IO_cleanup`: the bytes and their order on the descriptors match
  (d2ae23d).
- **Where:** `runtime/leanrt/src/io.rs`: `exit`, `main_exit`;
  `runtime/leanrt/src/lib.rs`: `uncaught_exception`; lean-runtime's
  `src/io/exit.rs` and `src/io/panic.rs`; `runtime/prelude.rr`: `l2r_exit`,
  `l2r_process_exit`.
- **Remove only if:** never.

### The program exports C trampolines the runtime calls back

- **What:** Every program defines `extern "C"` trampolines:
  `l2r_init_body`, `l2r_main_body`, `l2r_stderr_put_c` (the runtime's own
  diagnostics), `l2r_task_run_one_c` (a task's job runs the task through
  it) and `l2r_task_walk_c` (no longer called: lean-runtime walks
  dependents); programs that create promises also define
  `l2r_promise_drop_c` (a promise's last release). The runtime links some
  of them weakly.
- **Why:** The runtime cannot name generated code; calling through Rust
  also removes a Reussir-level call cycle through the stream code that
  crashed rrc ([Reussir bug 5](../../../reussir-bugs/05-one-armed-if.md)).
- **Where:** `Emit/Entry.lean`: `lowerEntry`; `Lower/Promises.lean`:
  `promiseResolveFn`, `taskDispatchFns`; `runtime/leanrt/src/io.rs`:
  `diag_put`.
- **Remove only if:** never.
