# Single externs in the runtime

Special cases inside the runtime's implementation of particular externs.
Paths are relative to the repository root.

### libm externs are lean-runtime's; some are called out of line

- **What:** Every `Float`/`Float32` libm extern (the prelude's `sin`, ...,
  `cbrt`, `atanhf`, under their C names) is a texture calling
  lean-runtime's `sem::libm::<name>`. Two groups are called through
  `leanrt::float::libm_call::<name>`, an `#[inline(never)]` wrapper of the
  same function: those whose operands lean-runtime hides with `black_box`
  (`exp2`, `pow`, the inexact `Float32` functions, `atan2f`, `powf`), and
  lean-runtime's ports of glibc's `cbrt`, `cbrtf`, `atanh`, `atanhf`
  (glibc 2.39's aarch64 results; lean-runtime defines them on every target
  since its 1c36a58, so leanrt's run-time panic for other targets is
  gone).
- **Why:** One runtime for both translators (owner decision): lean2rr has
  no libm code of its own. Before, the prelude used LLVM's intrinsics,
  which LLVM folds or rewrites on a known operand, one ulp away from glibc
  (cross-tests XT-3/XT-4; fixed first by calling glibc's functions through
  pointers looked up with `dlsym`, which this replaces; its test
  `RtFloatLibmFold` passes with lean-runtime's functions), and leanrt
  found glibc's `cbrt` with `dlopen`, because Rust's `compiler_builtins`
  defines its own `cbrt` ahead of libm. Out of line, because a Lean loop
  (a self-tail-calling Reussir function) that calls one of them otherwise
  keeps its tail call and grows the stack at every iteration: inlined,
  `black_box`'s stack slot escapes into the loop (100 million iterations
  of `Float.pow` overflowed the 1 GiB main stack); the ports are too big
  for a texture LLVM inlines, and a texture that is not inlined is a call
  through the packed-argument FFI boundary, whose argument slots have the
  same effect (2 million iterations of `Float.cbrt` overflowed a 1 MiB
  stack; review RULR-01). Cost: one more call than
  native Lean's direct call into libm (the wrapper, then lean-runtime's
  function; review RULR-05), to be measured in the owner-approved timing
  session. Tests: `RtFloatLibm`, `RtFloatCbrt` (glibc's `cbrt` against
  Rust's), `RtFloatLoopStack` (every libm function in loops on a 1 MiB
  stack), `tests/runtime/ffi-inline-check.sh` (no call through the FFI
  boundary and no `black_box` barrier in Reussir functions in those loops'
  IR), the libm rows of `rows-check.sh`.
- **Where:** `runtime/prelude.rr`: the libm section of `Float`;
  `runtime/leanrt/src/float.rs`: `libm_call`.
- **Remove only if:** lean-runtime marks these functions
  `#[inline(never)]` itself (agreed by lean-runtime's users): then the textures call
  `sem::libm` directly. Check `RtFloatLoopStack` and
  `ffi-inline-check.sh`.

### Strings, floats and fixed-width rules are lean-runtime's, through glue

- **What:** The prelude's textures call lean-runtime's `semantics` for
  hashes, string positions and comparisons, float formatting, bits,
  `frExp`, `scaleB`, classification and conversions, and the fixed-width
  rules with logic (`gen_scalars.py` makes those textures; single
  operations stay inline Reussir). The glue only converts: a big `Nat`
  position becomes `u64::MAX` (`l2r_pos_of_nat`), except for `next` and
  `prev`, which take a position below 2^63 (a big one stays the caller's
  `Nat` arithmetic, as in C), and `next`'s 2^63 becomes a big `Nat`
  (`l2r_nat_of_u64`); `get?`/`get!` give `0x110000` for `none`; a big
  `Int` for `scaleB` is `i64::MIN`/`MAX` by its sign (`l2r_int_sat_i64`);
  `leanrt::string::extract`/`extract_fast` make the string of
  lean-runtime's byte range (the string itself when the range is all of
  it); `leanrt::float::to_string` copies the bytes of lean-runtime's fast
  path (`float::to_string_fast_bytes`, a finite value below 2^53) and
  writes the other values' text into a 320-byte stack buffer (the longest
  `%f` of a double is 317 bytes; a longer text would go to the heap);
  `leanrt::string::utf8_count`, the count cached
  when a string is made, is lean-runtime's `utf8_strlen`, out of line for
  more than 16 bytes so that the textures that make strings stay small.
- **Why:** One runtime for both translators. Checked: lean-runtime's
  rows (1666 at the time) through a lean2rr build of its row oracle (`rows-check.sh`), the
  runtime tests, and `rrc --emit llvm-ir` on loops over `String.get`/`next`,
  hashes, floats and fixed-width rules: these textures are inlined into the
  Reussir code (no call through the FFI boundary: `ffi-inline-check.sh`);
  lean-runtime's cold paths (`get_core_cold`, `next_step_cold`,
  `frexp_i32`'s subnormal case, `scaleb_big`) are calls, as designed.
- **Where:** `runtime/prelude.rr`: the `sem::` textures, `l2r_pos_of_nat`,
  `l2r_int_sat_i64`, `lean_string_utf8_next`; `runtime/gen_scalars.py`;
  `runtime/leanrt/src/string.rs`: `extract`, `extract_fast`, `of_range`,
  `utf8_count`; `runtime/leanrt/src/float.rs`: `to_string`, `StackText`.
- **Remove only if:** lean2rr's representations change (the conversions
  follow them).

### Huge array sizes panic with Lean's message; a capacity reserves nothing

- **What:** The sizes are lean-runtime's rules (`sem::array`): an
  allocation of more than 2^24 elements checks what Lean's allocation would
  do (`leanrt::array::check_alloc`: `sem::array::alloc_bytes`, where
  `24 + elem * n` overflowing is `INTERNAL PANIC: integer overflow in
  runtime computation` and a size above `isize::MAX` `out of memory`; then
  a `mi_malloc` of that size failing is `out of memory`). Where the size is
  a `Nat`, a big one (2^63 or more) depends on the allocator, as in
  `lean.h` and `object.cpp`:
  - `Array.replicate` (`lean_mk_array`) takes any `n` below
    2^64 as the size (`l2r_replicate_len`, `sem::array::replicate_len`),
    so 2^63 … 2^64 − 1 overflow, and 2^64 or more is `out of memory`;
  - `Array.mkEmpty`/`emptyWithCapacity`, `ByteArray.emptyWithCapacity` and
    `FloatArray.emptyWithCapacity` (`lean_mk_empty_*`, inline in `lean.h`)
    never end the process: a capacity that cannot be reserved reserves
    nothing, and the result is the empty array (lean-runtime's LB-37,
    switch step 13; natively `out of memory` for every big `Nat` and the
    `replicate` ends below): the prelude's tag test releases a big `Nat`,
    and `leanrt::array::check_capacity` takes `sem::array::
    empty_with_capacity` and a `mi_malloc` probe for a small one
    ([../representations/arrays.md](../representations/arrays.md#a-capacity-that-cannot-be-reserved-reserves-nothing)).
  For `replicate`'s sizes: with 8-byte elements, 2^61 − 3 and up
  overflow, 2^61 − 4 is `out of memory`.
- **Why:** `replicate` took the `out of memory` path for every big `Nat`,
  where Lean overflows below 2^64 (cross-test XT-5, the `panics` fixture's
  row `array_replicate_nonscalar`; test `RtAllocBigNat`, which runs every
  allocator at the sizes around each boundary; `RtAllocOverflow`; and
  lean-runtime's `array/replicate.*`, `array/mkempty.*` rows through
  `rows-check.sh`). The capacity's inline tag test keeps the inline code
  at every `mkEmpty` small.
- **Where:** `runtime/prelude.rr`: `lean_mk_array`,
  `l2r_mk_empty_with_capacity`, `l2r_replicate_len`, `l2r_internal_panic`;
  `runtime/leanrt/src/array.rs`: `check_alloc`, `check_capacity`,
  `check_alloc_slow`, `capacity_slow`, `with_capacity_checked`, `replicate`;
  `runtime/leanrt/src/nat.rs`: `nat_replicate_len`.
- **Remove only if:** never (the messages are observable).

### `ByteArray.copySlice` takes its offsets saturated (LB-06 lifted)

- **What:** `lean_byte_array_copy_slice` passes the source offset, the
  destination offset and the length as `u64` (`l2r_nat_sat`: the value, or
  `u64::MAX` for 2^64 or more), returns `dest` inline for a source offset
  past the source's end, and the texture does lean-runtime's plan
  (`sem::array::copy_slice`: the bytes to copy, where, and the new size).
- **Why:** Natively `lean_nat_to_size_t` ends with `INTERNAL PANIC: out of
  memory` for an offset or length of 2^64 or more; the Lean definition has
  a value there, which both translators compute (LB-06, plan §10). Test
  `RtLiftedLimits` (`copySlice`), lean-runtime's `array/copyslice.*` rows.
- **Where:** `runtime/prelude.rr`: `lean_byte_array_copy_slice`,
  `l2r_nat_sat`; `runtime/leanrt/src/nat.rs`: `nat_sat_u64`;
  `runtime/leanrt/src/array.rs`: `copy_slice`.
- **Remove only if:** never.

### Panics and their texts are lean-runtime's

- **What:** `lean_panic_fn`'s output follows `sem::panic::panic_fn_plan`
  and is carried out by lean-runtime's executor, `io::panic::report`
  (`leanrt::panic_text`: the message, then `backtrace:` and lean-runtime's
  `NO_BACKTRACE` line unless `LEAN_BACKTRACE=0`, for Lean's current stderr
  stream; under `LEAN_ABORT_ON_PANIC`, to descriptor 2 after flushing
  stdout, then `abort`). Internal panics print
  `sem::panic::INTERNAL_PANIC_PREFIX` and the message of an
  `InternalPanic` (`leanrt::lean_internal_panic`; lean2rr's own invariant
  failures keep their own texts, `leanrt::internal_panic`) and end as
  `io::panic::internal_panic` does; `uncaught exception: ` and the
  stack-overflow text are lean-runtime's constants; the index-out-of-bounds
  message is `sem::array::INDEX_OUT_OF_BOUNDS`. `panic_text` and
  `lean_internal_panic` are `extern "C"`. Since switch step 8 the executor
  is lean-runtime's (below).
- **Why:** One runtime for both translators; lean-runtime's panic rows
  (`rows-check.sh`) check them. `extern "C"` (no unwinding): the prelude's
  texture is now one call, which LLVM inlines into the panicking code; a
  Rust function there would add a landing pad and change the caller's
  code (seen in Sieve's `main`: different registers and blocks), where the
  old texture was a call to it.
- **Where:** `runtime/leanrt/src/lib.rs`: `Collect`, `panic_text`,
  `lean_internal_panic`, `internal_panic`, `uncaught_exception`,
  `promise_dropped`, `lean_panic`; lean-runtime's `io::panic` and
  stack-overflow report (`sched::install_stack_overflow_handler`);
  `runtime/prelude.rr`: `l2r_internal_panic`,
  `l2r_panic_text`, `l2r_panic_code_text`, `l2r_process_exit`.
- **Remove only if:** never.

### IO is lean-runtime's, through glue (switch step 3)

- **What:** Every IO extern of Lean's library goes to lean-runtime's `io`
  module (features `io` and `proc-title`), through glue that only converts
  lean2rr's values: `leanrt::fs` (handles: an `LHandle` box holding
  lean-runtime's `Handle`, or none for a handle that is not open; the file
  system, temporary files, `IO.getEnv`, random bytes; the last-error slot),
  `leanrt::io` (the standard streams, the exit, the clocks, `timeit`'s and
  `allocprof`'s text), `leanrt::proc` (processes), `leanrt::sys`
  (`Std.Internal.UV.System` for the shim), `leanrt::rt` (the startup glue).
  leanrt's own implementations (`cfile.rs`, the old `fs.rs`, `io.rs`,
  `proc.rs`, `sys.rs`, the startup descriptors of `rt.rs`) are gone; the
  prelude's textures keep their names and signatures (but
  `l2r_stream_getLine`, which gets the string from leanrt, and the
  process and title primitives below), so programs' code is unchanged.
  - The last-error slot keeps the shape it had before (a `failed` flag read
    inline after every IO primitive, `l2r_io_ok`, and the code, read inline
    on every error path): `fs::set_err` takes lean-runtime's `IoError`
    apart into the `lean_mk_io_error_*` builder (`fs::kind_of`: its
    constructor, with or without a file name), the code (`error_code`), the
    file name and the details, which `fs::errno`, `error_kind`,
    `error_fname` and `error_details` give back.
  - Unbounded results go into a `Vec<u8>`, infallible as lean-runtime's
    contract asks of `getLine`'s sink (which appends under the stream's
    lock): a failed allocation aborts with Rust's message (status 134; native
    aborts with `std::bad_alloc`, 134), never exits (review RST3-02: a
    fallible sink there made a line without end spin forever; test
    `RtLineNoEnd`). Only a child's output (`IO.Process.output`) goes into
    lean-runtime's `StoppingSink` (switch step 5; leanrt's own `fs::Sink`
    before), which stops (`ByteSink::stopped`, so lean-runtime stops
    reading); the process then ends with `INTERNAL PANIC: out of memory`
    once the crate has returned (AR-5).
  - `IO.Process.output` is one primitive, `l2r_proc_output` (lean-runtime's
    `io::process::output`), with `l2r_proc_output_str`; lean2rr's
    generated drain, UTF-8 checks and `wait` are gone (`Lower/Process.lean`,
    `processOutputBody`). The `Child` operations find lean-runtime's
    process object by pid (`proc::CHILDREN`) until the child is reaped
    (`wait`, or a `tryWait` that sees it exit); a reaped child's pid gets
    the system call itself, as natively: `waitpid` (`ECHILD`), `kill` or
    `killpg` (`ESRCH`) (review RST3-04; test `RtProcessReaped`), through
    lean-runtime's object for the pid (`ChildProcess::from_pid`, switch
    step 5; leanrt's own `unsafe` system calls before). A child
    lean-runtime models because no stand-in could be started keeps its
    standard input's read end until it is reaped (lean-runtime's model of a
    stdin that takes a pipe's capacity, then fails with `EPIPE`); natively
    the failed child closes it when it exits.
  - The shim's `Std.Internal.UV.System` functions get lean-runtime's
    errors themselves, kept in the operation (switch step 5; at step 3 as
    libuv codes, which the shim decoded again); `setProcessTitle` reports
    lean-runtime's error.
  - Startup: an ELF constructor opens `io::startup`'s native descriptors
    (on failure LB-30, LB-31; `rt`'s own until switch step 7, lean-runtime's
    feature `startup-fds` since, below); `l2r_set_initializing(false)`
    is `mark_end_initialization`; `main`'s return (`l2r_exit`,
    `io::main_exit`) and an uncaught error call `io::exit::after_main`
    first; every normal end calls `io::exit::exit`; an uncaught error's
    text is `io::exit::show_error` (three writes, as natively;
    `io::panic::uncaught` since switch step 8).
- **Why:** One runtime for both translators (owner decision); lean-runtime's
  io was built from leanrt's own `FILE` model, file-system code and
  fork-based processes and the other translator's runtime, and fixes Lean bugs (LB-02, LB-03,
  LB-14, LB-15, LB-16, LB-17, LB-29, LB-30, LB-31). What stays lean2rr's,
  and why:
  - the current standard streams (`IO.setStdout` & co.): representation
    glue on the hot path (owner's decision, 2026-10-04). They are lean2rr's
    `IO.FS.Stream` records of closures, kept in generated cells
    (`stdStreamFns`) and set aside per task (`once::push_context`, as
    lean-runtime's `streams::swap_context` does); lean-runtime's `streams`
    stores a translator's Rust values, and `IO.println` reads the current
    stdout at every call, inline, where lean-runtime's slots would add a
    call through the FFI boundary to every print. The cells follow
    `io::streams`' semantics exactly: a thread (`main`, each task) starts
    with the process's streams, built on first use; `setStdout` & co.
    replace the current one and return the previous one; a task's streams
    are its own and the caller's come back when it ends; the runtime's own
    standard-error lines go through the current stderr's `putStr`
    (`l2r_stderr_put`), and to descriptor 2 while none has been set. They
    only store and swap values: lean2rr has no stream logic of its own, and
    every operation on a stream is lean-runtime's (the `l2r_stream_*`
    primitives over its standard-stream handles);
  - `IO.Process.forceExit` stays `_exit`: lean-runtime's `force_exit` is
    `std::process::exit`, which runs linked C code's exit handlers, and
    its documentation asks a glue that needs `_Exit` to call `_exit`
    (since step 4 after the context's handed-off streams are written,
    `io::force_exit`);
  - `IO.getTID` (`gettid`; lean-runtime has none);
  - the Windows time-zone errors stay the shim's Lean code (the same
    errors as lean-runtime's `time::windows_*`).
  Since step 4 (below) the effect points, `IO.sleep`/`dbgSleep` and the
  signal watchers are lean-runtime's too, and its IO cooperates with the
  scheduler (a read of a pipe, a `flock`, a `waitpid`, `output`'s `poll`
  let the other contexts run).
- **Tests:** the runtime suite's IO tests unchanged; `RtFdStartupNoUring`
  (no longer an expected failure), `RtTitleCmdline` (the title in
  `/proc/self/cmdline`: lean-runtime's constructor is linked),
  `RtStartupFdExhausted` (LB-30, LB-31, expectation files); lean-runtime's
  program cases through lean2rr's builds (`scripts/cases.py check
  --exe-dir`).
- **Where:** `runtime/leanrt/src/fs.rs`, `io.rs`, `proc.rs`, `sys.rs`,
  `rt.rs` (`run_main2`, `set_initializing`);
  `runtime/leanrt/src/lib.rs`: `uncaught_exception`; `runtime/prelude.rr`:
  the standard streams, files, processes, `timeit`, `allocprof`,
  `IO.getEnv`, `Std.Internal.UV.System`; `lean2rr/LeanToReussir/Lower/Process.lean`:
  `spawnCall` (`output?`), `processOutputBody`; `lean2rr/L2RShim.lean`:
  `setProcessTitle`; `scripts/l2r.py`: `LEAN_RUNTIME_FEATURES`.
- **Remove only if:** never.

### Tasks, `Std.Sync` and the event loop are lean-runtime's, through glue (switch step 4)

- **What:** lean2rr's tasks, promises, thunk waits, `Std.Sync`, effect and
  polling points, sleeps, `Std.Internal.UV`'s loop, timers, signals,
  sockets, name resolution and interfaces, and Lean's stack-overflow
  report run on lean-runtime's `sched` and `net` (features `sched`,
  `stack-overflow`, `net`); leanrt keeps the glue lean-runtime's
  `docs/sched.md` ("The glue") and `docs/net.md` ask for: `Glue::suspend`
  (the one `unsafe` dereference, with its entry), `switched` (the stream
  cells per context), `task_begin` (a task's own stream context), the
  task objects (cells, `leanrt::task`'s entries naming lean-runtime's
  `TaskId`s, the jobs that run them through the program's dispatcher,
  `release` at the program's last reference), the waits of lean2rr's own
  objects (a `busy` thunk, a constant another context computes),
  `before_publish` at cell stores, in a program that creates tasks the
  reference operations' points (`refs`: `ref_read`, `before_publish`, and
  Lean 4.35's wait while `modify` holds a reference), the scheduler's
  start on `main`'s thread at the first task (`start_with`; lean-runtime's
  `start_lazy` since switch step 7, below), `finish`
  after `main` (with `io::exit::after_main`), the stack-overflow handler
  on each thread that runs Lean code, the no-suspend scope around a stream
  handle's drop, promises dropped inside a free resolved once it is over,
  the event loop's completions through the shim's promises. leanrt's own
  scheduler (`sched.rs`, `task.rs`, `coro.rs`, `sync.rs`), its event loop
  and sockets (`net.rs`), its stack-overflow handler (`rt.rs`), and the
  shim's own checks are gone; the generated code is unchanged (its
  primitives map onto lean-runtime's API).
- **Why:** One runtime for both translators (owner decision; lean-runtime's
  `sched` was built from leanrt's). Lean bugs not reproduced, now
  lean-runtime's: LB-13 (a pool task enqueued after `main` runs), LB-19,
  LB-20, LB-21 to LB-28, LB-32, LB-33 and LB-34 (a timer's or signal
  watcher's `stop` or `cancel` and a `sync` dependent that subscribes
  again; lean-runtime's `docs/lean-bugs.md`), and LB-01 and LB-18 (a
  reference's `set` or `swap` during a blocked `modify`).
- **Tests:** the runtime suite's task, promise, `Std.Sync`, timer, signal
  and socket tests; lean-runtime's program cases of `tasks`, `sync`,
  `refs`, `uvloop`, `net`, `taskio` and the IO cases with tasks through
  lean2rr's builds (`scripts/cases.py check --translator lean2rr`).
- **Where:** `runtime/leanrt/src/task.rs`, `sched.rs`, `sync.rs`,
  `net.rs`, `refs.rs`, `persist.rs`, `once.rs`, `drop.rs` (`run`, `free_cell`),
  `fs.rs` (`close`), `rt.rs` (`install_stack_overflow_handler`), `io.rs`
  (`mono_nanos_polled`, `force_exit`); `runtime/prelude.rr` (the
  `l2r_task_*`, `l2r_lcell_set`, `l2r_ref_*`, `l2r_shim_*` textures);
  `lean2rr/LeanToReussir/Lower/Externs.lean` (`programCreatesTasks`,
  `refPoint`); `lean2rr/L2RShim.lean`; `scripts/l2r.py`:
  `LEAN_RUNTIME_BASE_FEATURES`.
  Implementation notes: [../tasks/](../tasks/README.md).
- **Remove only if:** never.

### A large read right after output writes the pending output first

- **What:** In lean-runtime's `FILE` model (`io::cfile`), a read of at
  least one buffer (the direct path of `xsgetn`) right after output on the
  same handle first writes the pending output, as `fflush` would; if that
  write fails, the read fails with its error. A failed seek back over
  read-ahead before the write (`ESPIPE`: a FIFO opened `readWrite` and read
  ahead) is no failed write: then, as glibc's direct read does, the pending
  output and the read-ahead are dropped and the read goes on, with `errno`
  restored to its value before the attempt (review RXT-06). Everything
  else follows glibc.
- **Why:** glibc's `_IO_file_xsgetn` resets the put area there and drops
  the pending output (C11 7.21.5.3p7 makes output directly followed by
  input undefined): written data never reaches the file. Judged a Lean
  runtime bug, LB-02 in lean-runtime's
  [docs/lean-bugs.md](https://github.com/QueClr/lean-runtime-rs/blob/main/docs/lean-bugs.md); the owner's ruling is not
  to reproduce it (review RXT-01 fixed the FIFO case, the same fix as
  lean-runtime io-1's af6ecf2; the model was leanrt's until switch step 3).
  Tests `RtReadAfterWrite`, `RtStdioStdoutRead` (expectation files
  `NAME.native.out`/`NAME.l2r.out`), `RtFifoReadAfterWrite` (the FIFO, the
  same as native), `RtFifoErrnoRestore` (the `errno` a later report sees);
  lean-runtime's differential test of the model against glibc
  (`tests/cfile_glibc.rs`).
- **Where:** lean-runtime's `src/io/cfile.rs`: `xsgetn`, `new_do_write`;
  plan §10, "Runtime: Lean bugs we do not reproduce".
- **Remove only if:** the owner rules to follow native here after all.

### A child's `null` stream is `/dev/null` opened by the parent

- **What:** For each `null` stream of `IO.Process.spawn` (so also
  `IO.Process.output`'s stdin without input), lean-runtime's
  `io::process` opens `/dev/null` in the parent (read-only for stdin,
  write-only otherwise) with `O_CLOEXEC`, after the pipes, and the child
  gets it as its stream; a failed open (`EMFILE`) is the spawn's error,
  `decode_io_error(errno, nullptr)` like a failed `pipe2`, and the
  descriptors made so far are closed.
- **Why:** Natively the forked child opens `/dev/null` without
  close-on-exec and never closes it after `dup2`, so the program inherits
  one more descriptor per `null` stream (LB-15), and it ignores a failed
  open, so `dup2(-1, n)` fails and the program runs on the parent's own
  descriptor n (LB-17). Both are judged Lean runtime bugs in lean-runtime's
  [docs/lean-bugs.md](https://github.com/QueClr/lean-runtime-rs/blob/main/docs/lean-bugs.md),
  not reproduced (plan §10). leanrt had the same fix in its fork-based
  `proc.rs` (fix-lb15-17) until switch step 3. Opening after the pipes
  keeps the pipes' descriptor numbers native's. One consequence: a spawn in
  which some `null` stream follows a piped one needs exactly one more free
  descriptor than natively (one in all, however many such streams), since
  the forked child has closed that pipe's other end by the time it opens
  `/dev/null` (lean-runtime's case `process/pipe_null_two_free` accepts
  both outcomes; review RLB-01). Tests `RtProcessNullFd`,
  `RtProcessNullOpenFails`, with expectation files
  `NAME.native.out`/`NAME.l2r.out`.
- **Where:** lean-runtime's `src/io/process.rs` (`setup_stdio`); plan §10,
  "Runtime: Lean bugs we do not reproduce".
- **Remove only if:** the owner rules to follow native here after all.

### `System.Platform.target` follows leanrt's target

- **What:** `lean_system_platform_target` returns lean-runtime's
  `semantics::toolchain::PLATFORM_TARGET`, put together by `cfg` from the
  target leanrt is compiled for: `aarch64-unknown-linux-gnu` or
  `x86_64-unknown-linux-gnu`, the triples the native Lean toolchains for
  those hosts report (`lean --version`). Any other target is a
  `compile_error!` of leanrt (`rt.rs`) naming what to check. The prelude's other platform answers are constants that rely on
  the same restriction: `isWindows`, `isOSX` and `isEmscripten` are false,
  `isLinux` (`lean_system_platform_linux`, new in Lean 4.34) is true, and
  `numBits` is 64 (`USize` is `u64` in the prelude).
- **Why:** Natively the triple is `LEAN_PLATFORM_TARGET` from the
  toolchain's `version.h` (`lean.h` inlines `lean_system_platform_target`;
  Lean's CMake takes it from `clang --print-target-triple`), so it is the
  triple of the platform the program is built for. The prelude used to
  hard-code `aarch64-unknown-linux-gnu`, which is wrong on an x86-64 host
  (fix-r9-misc). leanrt builds only for Linux with glibc on aarch64 and
  x86-64 (the glibc `FILE` model, lean-runtime's targets), hence the error
  elsewhere instead of a guess. Test
  `tests/runtime/RtPlatform.lean` compares the triple, the word size, the
  three flags and the version strings with native.
- **Where:** lean-runtime's `src/semantics/toolchain.rs`;
  `runtime/leanrt/src/rt.rs` (the target guard); `runtime/prelude.rr`:
  `lean_system_platform_target`, `l2r_platform_target`,
  `lean_system_platform_windows`/`osx`/`linux`/`emscripten`,
  `lean_system_platform_nbits`.
- **Remove only if:** never; extend the guard (and review the constants)
  when leanrt gains a target.

### The version and git hash are the pinned toolchain's constants

- **What:** `Lean.githash` (`lean_get_githash`: the toolchain's commit)
  and `Lean.version.specialDesc` are lean-runtime's
  (`semantics::toolchain::GITHASH`, `SPECIAL_DESC`);
  `Lean.version.major/minor/patch/isRelease` (so `Lean.versionString` and
  `Lean.toolchain`) and `Lean.Internal.isStage0/hasLLVMBackend` are
  prelude constants of the toolchain lean2rr is built with, v4.34.0
  (`lean2rr/lean-toolchain`).
- **Why:** Natively they are compile-time constants of the toolchain's
  runtime (`version.h`); a program built by lean2rr must answer what the
  same program built natively answers.
- **Where:** `runtime/prelude.rr`: `lean_get_githash`,
  `lean_version_get_*`, `lean_internal_*`; test `RtPlatform`; leanrt's
  unit test `tests::lean_runtime_version_is_the_preludes` (`runtime/leanrt/src/lib.rs`)
  checks that `lean_version_get_major/minor/patch` spell the version the
  pinned lean-runtime mirrors (`lean_runtime::LEAN_VERSION`).
- **Remove only if:** never. Update them with every toolchain change;
  `RtPlatform` fails otherwise.

### Runtime functions both translators had are lean-runtime's (switch step 5)

- **What:** leanrt and the prelude call lean-runtime where they kept a copy
  of a runtime function lean-runtime has (its shared-1 batch, the
  redundancy audit of 2026-10-05): the toolchain facts
  (`semantics::toolchain`); `String.push`'s and `String.set`'s encoder
  (`semantics::string::push_unicode_scalar`, inline in their slow paths)
  and the lossy decoding of bytes (`lossy_utf8`); `IO.Process.output`'s
  sink (`io::StoppingSink`); `IO.Error`'s accessors and builder number
  (`IoError::os_code`, `file_name`, `details`, `builder_index`); the
  system clock in nanoseconds (`io::time::current_time_nanos`),
  `IO.monoMsNow` (`io::env::mono_ms_now`, after the polling point),
  `IO.getTID` (`io::env::get_tid`, the scheduler's thread number
  included, so the generated code no longer adds it); `allocprof`'s and
  `dbgTraceIfShared`'s texts (`io::debug::allocprof_text`,
  `shared_rc_line`); a reaped child's system calls
  (`io::process::ChildProcess::from_pid`); `Task.get`'s rule in a `sync`
  task (`sched::await_task`); the abort when `main`'s thread cannot be
  made (`sched::thread_create_failed`, whose line ends with `: <strerror>`
  as native's); `Std.Internal.UV.System`'s errors (passed on as
  `IoError`s instead of libuv codes the shim decoded again) and
  `Std.Time.Database.Windows`'s errors (`io::time`). leanrt's unit test of
  the 141 decoded errnos went to lean-runtime's; leanrt keeps a test of its
  last-error slot's wiring and one that its builder numbering is
  lean-runtime's.
- **Why:** The owner's rule: each translator keeps its own layout, and
  every shared runtime function lives in lean-runtime, once. Behaviour
  changes only where judged: the thread-creation text gains native's
  `: <strerror>` (the judge's verdict on audit item 5.14), and
  `TCP.Socket.new`/`UDP.Socket.new` report lean-runtime's error as an
  `IO.Error` (natively too) instead of an internal panic (verdict 5; libuv
  1.48 never fails there).
- **Where:** `runtime/leanrt/src/string.rs`, `fs.rs`, `fs_tests.rs`,
  `proc.rs`, `io.rs`, `rt.rs`, `task.rs`, `sys.rs`, `net.rs`, `lib.rs`
  (tests); `runtime/prelude.rr`; `lean2rr/L2RShim.lean`;
  `lean2rr/LeanToReussir/Lower/LazyGlue.lean` (`IO.getTID`).
- **Remove only if:** never.

### lean2rr's waits and deferred resolutions are lean-runtime's wait cores (switch step 6)

- **What:** leanrt's own copies of three wait protocols moved onto
  lean-runtime's wait cores (its wait-1 batch, `docs/sched.md`, "The wait
  cores"), in their keyed form, since lean2rr's Reussir records have no
  room for a waiter list:
  - a computation another context runs (core 3.1): a `busy` thunk waits
    with `wait_running_keyed` and wakes its waiters with `done_keyed`,
    under its address; a constant's claim is `step_keyed` and its store
    `done_keyed`, under `(slot << 1) | 1` (leanrt's `THUNK_WAITERS` and
    `CLAIMS` are gone);
  - a reference in a program that creates tasks (core 3.2): the points,
    `take`, and the wait or closing store are `ref_keyed`'s (leanrt's
    taken-reference registry is gone); the closing store is found at run
    time by the taking frame (option B), so the generated code is
    unchanged;
  - a promise dropped unresolved inside a free (core 3.3): its
    resolution, the cell's store included, is put off with `defer` when
    the free reaches it and run with `run_deferred` at the drain's end
    (leanrt's `later` list, `run_later` and its settle points are gone); a
    resolved one releases its task's cell there and then, in the free's
    order (review RS6-01).
  Reussir's patch 40-a (the drain-end hook) is required: `scripts/l2r.py`
  checks for it and leanrt names its symbol. lean-runtime pinned at
  `528fcbb` (wait-1; fixes-5's `IO.getTID`: a pool task gets its emulated
  worker's thread id, a dedicated task a new one, through
  `io::env::get_tid`, which lean2rr calls since step 5; fixes-6: a claim
  or a store before the task manager runs builds no scheduler state, so a
  program without tasks still pays nothing for the scheduler).
- **Why:** The owner's rule: runtime logic lives in lean-runtime once.
  Behaviour changes, judged: the taker's own `get` and `take` during its
  `modify` wait, as natively the program hangs there (review RS4-01, test
  `RtRefOwnGetDuringModify`; they read the placeholder before); a store
  from a `sync` dependent nested inside `modify`'s function waits, as in
  Lean 4.35 (LB-01); a promise a free dropped looks unresolved until its
  dependents run (the store-with-resolve shape, lean-runtime's review
  RW1-05; test `RtPromiseFreeLaterUnresolved`). No wait core is reached inside a free (W3:
  debug assertion `drop::assert_not_in_free`; test `RtPromiseFreeDepWaits`).
- **Tests:** `RtRefOwnGetDuringModify`, `RtPromiseFreeDepWaits`,
  `RtPromiseFreeLaterUnresolved`, `RtPromiseResolvedFreeOrder`,
  `RtWaitInline` and `tests/runtime/wait-inline-check.sh` (the points, a
  thunk's store and `done_keyed` inline in the executable's loops), the
  suite's thunk, constant, reference and promise tests; lean-runtime's
  task-area cases through lean2rr.
- **Where:** `runtime/leanrt/src/sched.rs` (`on_finish`,
  `thunk_wait_busy`), `once.rs` (`claim_cold`, `set_raw`), `refs.rs`,
  `task.rs` (`Promise`, `defer_promise_drop`, `resolve`, `hook_drained`,
  `drained`, `settled`), `drop.rs` (`run`, `assert_not_in_free`);
  `scripts/l2r.py` (`check_reussir_patches`).
  Implementation notes: [../tasks/cells.md](../tasks/cells.md),
  [../tasks/dependents.md](../tasks/dependents.md),
  [../tasks/scheduler.md](../tasks/scheduler.md).
- **Remove only if:** never.

### lean2rr's startup logic is lean-runtime's (switch step 7)

- **What:** Three pieces of startup logic only leanrt kept moved into
  lean-runtime (its shared-2 batch, f618102; audit items 4.2, 4.3, 4.5),
  and leanrt's copies are gone:
  - `main` on a thread of its own (4.2): `rt::run_main2` gives `main`'s
    body to `io::startup::run_main(sched::thread_stack_size(), ...)`,
    whose first step installs Lean's stack-overflow report; a Rust panic
    that unwinds out of the body comes back as `Err` and ends the process
    with status 101, its streams written: only one in the glue's own
    frames (the closure, `install_stack_overflow_handler`), since a panic
    inside the generated code (`l2r_main_body` and below) cannot unwind
    and aborts (status 134, buffered stdout lost), in both modes, as
    before. `rt::main_on_thread` asks
    `io::startup::main_on_thread`. leanrt's `run_body`, `MAIN_ON_THREAD`,
    `main_stack_size` and the unused `run_main` are gone;
  - the startup descriptors (4.3): lean-runtime's feature `startup-fds`
    (in `LEAN_RUNTIME_BASE_FEATURES`), its own ELF constructor in
    `.init_array.00101` (after `proc-title`'s 100, AR-20), opens them
    before Rust's runtime starts; `run_main2` calls
    `io::startup::ensure_native_descriptors()` first, which keeps the
    constructor linked and, if it did not act, opens them where they land.
    leanrt's constructor (plain `.init_array`), the `fcntl` and `close`
    externs, `DESCRIPTORS_RESERVED`, `open_startup_descriptors`,
    `is_rust_dev_null` and `reserve_native_descriptors` are gone;
  - the lazy start (4.5): `task::start` is `sched::start_lazy(LeanrtGlue,
    lean_num_threads(), thread_stack_size())`, `task::deferring` is
    lean-runtime's `deferring`, `task::shutdown` is `finish`;
    lean-runtime's entry points start the scheduler themselves
    (`ensure_started`), and the start turns `ST.Ref` read yields on.
    leanrt's `DEFERRING`, `MAIN_STARTED`, `WORKERS`, `STACK`,
    `SCHED_STARTED`, `ensure_started`, `start_sched`, `sched_started`,
    `sched::start`, `sync.rs`'s `settle`, and the `ensure_started` calls
    in front of `promise_new`, `register` and the `Std.Sync`, loop, timer,
    signal and socket constructors are gone.
  The prelude and lean2rr are unchanged: the generated entry still calls
  `rt::run_main2`, `rt::main_on_thread`, `task::start`,
  `task::deferring` and `task::shutdown`, now thin glue. leanrt's
  workaround for an allocation made before mimalloc's constructor
  (`alloc::heap_on_huge_pages`, dev eb0ea40) is gone too: lean-runtime's
  constructors no longer allocate (AR-36), and the page faults stay at
  their fixed level without it ([../startup/entry.md](../startup/entry.md)).
- **Why:** The owner's rule: runtime code lives in lean-runtime, once;
  leanrt keeps only lean2rr's layouts and glue. Behaviour changes, from
  lean-runtime's versions:
  - `main`'s thread has no name of its own: it keeps the process's
    (`/proc/thread-self/comm`), as native's `lthread`; leanrt named it
    `main`. A Rust panic's header (a runtime bug) on that thread now says
    `thread '<unnamed>'` where it said `thread 'main'`; what the panic
    does is unchanged (inside the generated code, an abort with status 134
    in both modes, as before; review RS7-01);
  - when the constructor did not act (under `ld.so ./prog`, without
    `/proc`, or in a shared library: lean-runtime's accepted deviations,
    RSH2-02, RSH2-11), the descriptors open at `main`'s start where they
    land, and a standard descriptor closed at startup stays Rust's
    `/dev/null`: leanrt's fallback closed the read-write `/dev/null`s on
    descriptors 0 to 2 first, which lean-runtime does not keep (a safe
    function that closes descriptors it does not own; reviews RSH2-04,
    LS2-01). In a normal launch the constructor acts, and the descriptors
    are native's, as before;
  - the lazy start's state is the thread's own (thread-locals) where
    leanrt's flags were process-wide: lean2rr runs Lean code on one thread
    at a time, and `task::start`, `main` and `task::shutdown` all run on
    `main`'s, inside `run_main`'s body;
  - a recursive mutex an initializer kept locked, locked again by `main`
    (fixes-7; dev 698e92b had the bug too): with `LEAN_MAIN_USE_THREAD=0` the
    lock is nested and the program goes on, and on `main`'s own thread
    `main` waits forever, also with `LEAN_NUM_THREADS=0`, as natively;
    before, the first hung and the second, with `LEAN_NUM_THREADS=0`, took
    the lock.
  lean-runtime's constructors use no global allocator (AR-36).
  lean-runtime pinned at `471f458` (shared-2, then fixes-7: a `Std.Sync`
  lock's owner names its OS thread instead of whether the scheduler has
  started, AR-39, review RS7-02; test `RtRecMutexInitOwner`).
- **Tests:** the runtime suite's startup, descriptor, title, stack and
  `LEAN_MAIN_USE_THREAD` tests (`RtFdLimit`, `RtFdStartupNoUring`,
  `RtStartupFdExhausted`, `RtStartupInit*`, `RtTitleCmdline`,
  `RtSignalFd`, `RtClosedStreams`, `RtInitRedirectNoThread`, `RtStack`,
  `RtStackOverflow*`, `RtThreadCreateFails`, and the new
  `RtMainThreadComm`: `main`'s thread keeps the process's name, and with
  `LEAN_MAIN_USE_THREAD=0` `main` runs on the process's main thread), and
  its task, constant, thunk, reference and `Std.Sync` tests
  (`RtRecMutexLazyStart`, `RtRecMutexInitOwner`, `RtTaskNoManager`);
  strace of startup against native.
- **Where:** `runtime/leanrt/src/rt.rs` (`run_main2`, `main_on_thread`),
  `task.rs` (`start`, `deferring`, `shutdown`), `sched.rs` (`LeanrtGlue`),
  `sync.rs`, `net.rs`, `alloc.rs`; `scripts/l2r.py`: `LEAN_RUNTIME_BASE_FEATURES`;
  lean-runtime's `src/io/startup.rs`, `src/io/startup_fds.rs`,
  `src/sched/mod.rs`. Implementation notes:
  [../startup/entry.md](../startup/entry.md),
  [../tasks/scheduler.md](../tasks/scheduler.md).
- **Remove only if:** never.

### The panic and exit executor is lean-runtime's (switch step 8)

- **What:** leanrt's copy of the code that carries out a panic's plan, and
  the other ends of a program, moved onto lean-runtime's `io::panic` (its
  shared-3 batch, 4deda83; redundancy audit item 3.4). leanrt's
  `panic_settings`, `panic_lines` and `panic_end` are gone, and its entry
  points forward:
  - `panic_text` (`panicCore`) and `lean_panic` (the runtime's
    `lean_panic`: `Task.get` in a `sync` task, `Promise.result!` of a
    dropped promise) call `io::panic::report(msg, force_stderr, glue)`,
    which reads the settings at each panic, makes the effect point, picks
    the stream, flushes stdout before the process's stderr, writes the
    lines there, and aborts or exits;
  - `lean_internal_panic` and `internal_panic` call
    `io::panic::internal_panic(msg, &mut Native)`;
  - `uncaught_exception` calls `io::panic::uncaught(msg, &mut Native)`
    (`after_main`, the line, status 1);
  - the prelude's `l2r_process_exit` (`IO.Process.exit`) calls
    `io::panic::process_exit(code, &mut Native)` (the effect point, then
    the exit), the only prelude texture that changed.
  The glue `Collect` (leanrt's `PanicGlue`) keeps two choices of lean2rr's
  (lean-runtime docs/panic.md, rows 3 and 4): the lines of a panic that
  goes on are collected and written with one `putStr` of Lean's current
  stderr stream (`panic_text` returns them to the prelude, which writes
  them through `l2r_stderr_put`; `lean_panic` through `io::diag_put`), as
  before; and `panic_text` makes its effect point only when the lines go
  to the process's stderr (on Lean's stream the default stream's `putStr`
  has one). Every other method is the executor's default, which is what
  leanrt did: the process's stderr and stdout are lean-runtime's models,
  the abort is `std::process::abort`, the exit is lean-runtime's `exit`.
- **Why:** The owner's rule: runtime code lives in lean-runtime, once;
  leanrt keeps only lean2rr's layouts and glue. Behaviour changes, from
  lean-runtime's executor:
  - the internal panic builds its line on the stack and writes it
    straight to descriptor 2, with no allocation (before: a `Vec`,
    allocated and grown twice, then lean-runtime's `stderr` model, whose
    first use allocates its one-byte buffer, and with tasks, when
    contended, the cooperative lock's bookkeeping; counted with gdb from
    `lean_internal_panic` to the process's end: four allocator calls
    before, none now). The bytes
    are the same, in one `write` (every message is under 256 bytes; the
    message stops at a NUL byte, as native's `%s`, and no lean2rr message
    holds one). Without tasks, promises, timers or watches the line is
    written under the same `stderr` lock as before, so it never lands
    inside another write in progress;
  - when this thread holds `stderr`'s lock already (an internal panic
    raised during its own write to `stderr`), the line is written at once
    and the exit's flush skips `stderr`; before, both waited for good
    (lean-runtime's `tests/io_panic.rs`, case `internal_while_holding`).
    No lean2rr program reaches this case: the only way would be an
    allocation failure inside that write, and a Rust allocation failure
    aborts through `handle_alloc_error` instead (review RS8-02);
  - once the program has a task, a promise, a timer or a watch (the
    cooperative locks on; the test is process-wide, so on every thread),
    the line is written without the lock: it does not wait for a write to
    `stderr` in progress by another context (a task or `main`, suspended
    in the middle of it on a full pipe), and, from the thread that drains
    `IO.Process.output`'s stdout after a failure (its out-of-memory end,
    case `process/output_drain_oom`), for any write to `stderr` in
    progress, `main`'s blocked write included. The line can then land
    inside that write, where before it waited (cooperatively on the
    scheduler's thread, with the plain lock on the drain thread), as
    natively the line waits for the other thread's `FILE` lock. A
    recorded deviation of lean-runtime's (docs/panic.md, row 10): the
    cooperative lock allocates and may switch contexts, which the
    out-of-memory end must not, and a plain lock off the scheduler's
    thread could wait for good for a context suspended in the middle of
    its write, which only that thread resumes (review RS8-01, judged: a
    hang ranks above the place of a line in an error path; lean-runtime's
    note AR-45). Only the place of the line in stderr's bytes changes
    (plan §10, "Runtime"). Probe: a task's
    200001-byte write to stderr into a pipe read only after a second, and
    an internal panic of `main` meanwhile: the line at byte 65536 (the
    pipe's size), natively and before at byte 200001;
  - a panic's lines on the process's stderr (abort mode, `force_stderr`)
    are written line by line, each line then its newline, as native's
    `std::cerr`; before, one `write` for all of them. Same bytes, same
    order.
  Nothing else changes: the collected lines, the effect points, the
  flush, the settings read at each panic, the abort, `exit(1)`, the
  uncaught line and `IO.Process.exit`. The generated code is unchanged
  but for the prelude's `l2r_process_exit` texture (and two comments).
  lean-runtime pinned at `e34cd61` (main: shared-3 with tests-1, 45679c6,
  test-only; perf-1, 109a9c3: AR-40, a constant's claim and a reference's
  keyed take keep their first entries inside the thread-local, so they
  allocate nothing; and net-threads, e34cd61: networking in threads mode,
  where lean2rr's single-thread build makes the same calls as before
  through the crate's mode layer, and `SendData` and `RecvBuf` gain the
  supertrait `MaybeSend`, empty and blanket in single-thread mode, so
  leanrt's `impl SendData for Bufs` is unchanged).
- **Tests:** the runtime suite's panic, internal-panic, uncaught-error,
  exit, abort, initialization, promise and stack tests (`RtPanic`,
  `RtPanicOrder`, `RtAbortPanic`, `RtInternalPanic`, `RtLiftedLimits`,
  `RtAllocOom`, `RtCastSorry`, `RtThrow`, `RtStdioUncaughtNul`, `RtExit`,
  `RtExitFlush`, `RtStdioExitOrder`, `RtTaskExit`, `RtInit*`,
  `RtStartup*`, `RtPromise*`, `RtStack*`), the `Std.Sync` and stream
  redirection tests, the network tests (`RtTcp`, `RtUdp`, `RtSockCancel`,
  `RtNetAddr`, `RtNetEffectPoll`; net-threads); the unit test
  `tests::panic_lines_are_collected_for_one_put` (the glue's one text);
  lean-runtime's panic rows (`rows-check.sh`) and its cases
  `tasks/promise_in_initialize` and `_abort` through lean2rr.
- **Where:** `runtime/leanrt/src/lib.rs` (`Collect`, `panic_text`,
  `lean_internal_panic`, `internal_panic`, `uncaught_exception`,
  `lean_panic`); `runtime/prelude.rr` (`l2r_process_exit`);
  lean-runtime's `src/io/panic.rs` and `docs/panic.md`.
- **Remove only if:** never.

### A wait for a pure task that the worker starts during the wait no longer hangs (switch step 9)

- **What:** lean-runtime pinned at `83f7127` (main: tests-2, 6786aa6,
  test and doc changes only, among them LB-35 under "Not bugs" in its
  `docs/lean-bugs.md`; and fixes-8, 83f7127: a hang in the scheduler's
  wait). The fix is in lean-runtime's `may_run_awaited`, the rule that
  decides whether a waiter runs the awaited task on its own stack. Before
  it decides, the rule lets the worker that an earlier enqueue woke take
  what it would have taken by now (`settle_worker`: 90 µs after the
  enqueue for the first worker, 20 µs later on). A worker only marks a
  pure task started (`pick`), and the mark wakes the task's waiters. When
  the worker takes the awaited pure task there, the mark comes before the
  waiter has blocked, so its wake-up reaches nobody. The rule now checks
  the mark again and runs the task on the waiter's stack, as for any
  awaited started task. Before, the waiter blocked on the started task
  with no wake-up to come: the hub starts a started pure task by itself
  only as its last resort (`last_resort`), which a watched descriptor
  prevents for good, and a pending sleep or timer until it ends. So with
  a socket open the hub waited in `epoll_wait` forever, and without one
  the wait was delayed until every pending sleep or timer had ended (a
  `Task.get` waited out an unrelated `IO.sleep`: 500 ms instead of 2 ms
  in the crate review's probe). leanrt, the prelude and the generated code are
  unchanged.
- **Why:** A hang where native Lean finishes: `RtTcp` hung about one run
  in 20 (natively 0 in 100). The window: a pure task spawned while the
  worker is idle, more than 90 µs without a scheduler call, then a wait
  for that task, with a descriptor watched. Test `RtTaskPickedInWait`: a
  listening socket kept open until `main`'s last line, a pure
  `Task.spawn`, about a millisecond of computation without an effect
  point (`IO.lazyPure`), then `Task.get`; it hung in 8 of 8 runs with
  lean-runtime e34cd61 and passes with 83f7127, as natively. The socket
  must still be used after the wait: a socket last used at `listen` is
  freed and closed right after it, nothing is watched, and the last
  resort runs the task.
- **Tests:** `RtTaskPickedInWait`; `RtTcp` (50 runs, no hang); the
  runtime suite's task, promise and network tests; lean-runtime's unit
  test `a_pure_task_the_worker_starts_in_the_waiters_look_runs_there`.
- **Where:** lean-runtime's `src/sched/task.rs` (`may_run_awaited`,
  `settle_worker`, `pick`, `last_resort`) and `docs/sched.md` ("The
  pure-task rule"). Implementation notes:
  [../tasks/scheduler.md](../tasks/scheduler.md).
- **Remove only if:** never.

### The runtime library's speed items of an instruction profile (switch step 10)

- **What:** lean-runtime pinned at `e5e502e` (main: fixes-8b, 1a21a63:
  tests, docs and a debug assertion in the scheduler's wait; perf-2,
  e5e502e: `Float.toString`'s exact fast path and `BigInt`'s word
  methods). `Float.toString` writes a finite value below 2^53 in magnitude
  from `round_half_even(|x| * 10^6)`, computed exactly in integers, instead
  of Rust's `{:.6}`, which fell back to the bignum Dragon algorithm for
  values with few significant digits; the text is unchanged. The `Int`
  rules call a word method (`add_i64`, `i64_sub`, `mul_i64`, `tdiv_i64`,
  ...) when one operand is a word and the other big; leanrt's `GInt`
  overrides all eleven with its in-place limb code (`big::add_limb`,
  `mul_limb`, `div_limb`), so the word needs no block (see
  [../representations/nat-int.md](../representations/nat-int.md#the-slow-paths-are-lean-runtimes-rules-on-lean2rrs-numbers)).
  The same step changes four things of leanrt and the prelude: no
  `mi_good_size` call up to 64 bytes
  ([../representations/arrays.md](../representations/arrays.md#a-blocks-capacity-is-mimallocs-size-class-without-a-call-up-to-64-bytes)),
  the equality of a small and a big `Int` without a call
  ([../representations/nat-int.md](../representations/nat-int.md#int-equality-of-a-small-and-a-big-word-needs-no-call)),
  the block test of string equality
  ([../representations/strings.md](../representations/strings.md#string-equality-tests-the-same-block-first))
  and the release of a record an array set replaces
  ([../ownership.md](../ownership.md#a-set-releases-a-replaced-record-with-its-decrement-in-line)).
- **Why:** An instruction-count profile of the 18 classic programs
  (cachegrind, no timing) found the runtime library's share large
  in strings (about 30%, `Float.toString`), liasolver (25%, `Int` beyond
  `int32`), unionfind (7%, a set texture not inlined) and monadic-interp
  (6.5%). Measured with cachegrind at the small sizes (instructions,
  without mimalloc's free-path functions, whose counts vary from run to
  run): the pin alone, strings 19.8% fewer and liasolver 0.8%; the word
  methods' overrides, liasolver 4.6% fewer; the whole step against dev,
  liasolver 14.7% fewer, strings 19.9%, monadic-interp 1.9%, qsort
  0.15%, and unionfind 4.6% more: a set that frees the record it replaces
  now frees it in Lean's order through the runtime's free (review
  RS10-01), about 140 instructions per free (about 74 since switch step
  11, next section)
  ([../ownership.md](../ownership.md#a-set-releases-a-replaced-record-with-its-decrement-in-line)).
- **Tests:** leanrt's unit test `big::tests::word_methods_match_defaults`
  (each override against the trait's default, big operands at the word
  ranges' edges and zero, unique and shared); the runtime suite's `Int`,
  `Nat`, `Float`, `String` and array tests; `tests/runtime/rows-check.sh`
  (lean-runtime's `Int` and `Float` rows through lean2rr); the new tests
  `RtIntSmallBigEq`, `RtArraySets`, `RtArrayRecordFreeOrder`,
  `RtArraySetFreeOrder` and `RtArrayPopFreeOrder`.
- **Where:** lean-runtime's `src/semantics/float.rs` (`to_string`,
  `fixed6`), `src/semantics/bignum.rs` (the word methods) and
  `src/semantics/int.rs` (`ring_op!`, `div_slow`); leanrt's
  `runtime/leanrt/src/big.rs` (`impl BigInt for GInt`, `add_limb`,
  `div_limb`).
- **Remove only if:** never (speed only); the overrides must give the
  defaults' values (the unit test).

### A record's last reference is one pending cell; one-shot signal watchers (switch step 11)

- **What:** lean-runtime pinned at `dce982d` (main: fixes-9, 8dc5224;
  fixes-10, 6de95aa; cases-1, 68a32e6 and 927922b, the crate's case
  tooling and expectations; fixes-11, dce982d). The fixes change only
  `src/sched/uv_signals.rs`, the delivery of signals to one-shot watchers
  (`Std.Internal.UV.Signal.mk n false`, natively `SA_RESETHAND`): a signal's handler
  checks the flag the loop can change before its byte wakes the loop, and
  each one-shot registration's reset is a pair on a fresh flag of its own
  (fixes-9); a one-shot registration delivers one signal, and the loop
  drops a later one until the next registration, as the kernel's default
  action after the reset discards a signal it ignores (fixes-10); a later
  signal of a spent registration whose default action ends the process
  ends it, and a signal that came before a one-shot re-registration does
  not spend it (fixes-11). No API change: leanrt, the prelude and the
  generated code are unchanged by the pin. The same step frees the last
  reference to a record that a set, a pop or a reference or cell set
  gives up as one pending cell of Reussir's stack instead of a step
  ([../ownership.md](../ownership.md#the-last-reference-to-a-record-is-freed-as-one-pending-cell)).
- **Why:** The pin: a one-shot watcher started in a dependent of another
  one-shot watcher's promise got a second signal that natively the reset
  discards, a stopped last watcher between the loop's wake-up and the
  handler's check could end the process, and a signal that came before a
  one-shot re-registration spent it, so the loop dropped the next one
  (the crate's cases `uvloop/signal_reset_*`). The free: about 74 instructions per freed
  record instead of about 140; unionfind 0.8% more instructions than dev
  d39294a (step 10: 5.0% more than d39294a), the same release order.
- **Tests:** `RtSignal`, `RtSignalFd`, the timer and network tests
  (`RtTimer`, `RtTimerSyncSleep`, `RtTimerPeriod0`, `RtTimerStopDropped`,
  `RtTcp`, `RtUdp`, `RtSockCancel`, `RtNetEffectPoll`, `RtUvSysLimits`,
  `RtTaskEffectRounds`, `RtSystem`); leanrt's unit tests
  `drop::tests::record_free_order` and `record_free_inside_a_free`; the
  new test `RtArraySetFreeNested`; the free-order tests
  (`RtArraySetFreeOrder`, `RtArrayPopFreeOrder`, `RtArrayRecordFreeOrder`,
  `RtDropOrder*`, `RtPromise*FreeOrder`, `RtPromiseFreeLaterUnresolved`,
  `RtRefSet*`).
- **Where:** lean-runtime's `src/sched/uv_signals.rs` and `docs/sched.md`;
  leanrt's `runtime/leanrt/src/drop.rs` (`free_unique`, `release_unique`,
  `release_record`) and `runtime/leanrt/src/array.rs` (`release_last`).
- **Remove only if:** never.

### The runtime library's speed items of a second profile (switch step 12)

- **What:** lean-runtime pinned at `2910ef7` (main: perf-3, 2910ef7:
  `to_string_fast_bytes`, the word-at-a-time `utf8_strlen`). With it,
  three changes of leanrt: a big `Int` in the `i64` range is computed as
  a word
  ([../representations/nat-int.md](../representations/nat-int.md#a-big-int-in-the-i64-range-is-computed-as-a-word)),
  a substring of an ASCII string takes its count from its length, and
  `Float.toString` copies the rule's bytes
  ([../representations/strings.md](../representations/strings.md#a-substring-of-an-ascii-string-takes-its-count-from-its-length)).
- **Why:** A second instruction-count profile of the 18 classic programs
  (cachegrind, small sizes, the same attribution as step 10's) found the
  runtime library's share still large in liasolver (21%: `Int` beyond
  `int32`) and strings (12%: substrings, `Float.toString`), and under 5% in
  the others. Against dev 7bfc758, the run with the fewest instructions of
  each binary (mimalloc's free path differs from run to run, see below):
  liasolver 6.5% fewer, strings 2.9% fewer, sieve 1.6% fewer (a side
  effect: LLVM compiles `main` differently), bignum 0.03% more (the range
  test on its big operands), the others within 0.15%. mimalloc's free
  path: Reussir's `ReussirGlobalAlloc` asks for 16-byte alignment for
  every Rust allocation (`mi_malloc_aligned`), and with
  `MI_MAX_ALIGN_SIZE=8` a request whose size class is not a multiple of 16
  can be over-allocated, which marks its page as holding aligned blocks;
  every later free in that page then takes `mi_free_generic_local` and
  `_mi_page_ptr_unalign`. Which page it is changes from run to run: up to
  8% of monadic-interp's instructions, 5.5% of unionfind's, 2.5% of
  liasolver's.
- **Tests:** leanrt's unit tests `nat::tests::narrowed_operands`,
  `float::tests::to_string_is_the_rules_text` and the extended
  `string::tests::counts_follow_every_update`; lean-runtime's
  `semantics::string::tests::utf8_strlen_counts_every_length_and_position`
  and its float tests on `to_string_fast_bytes`; the new runtime tests
  `RtIntWordBand` and `RtStringExtractCount`; `RtInt`,
  `RtIntSmallBigEq`, `RtFloat`, `RtFloatLits`.
- **Where:** leanrt's `runtime/leanrt/src/nat.rs`, `string.rs` and
  `float.rs`; lean-runtime's `src/semantics/string.rs` and
  `src/semantics/float.rs`.
- **Remove only if:** never (speed only).

### Lean runtime bugs and a limit the crate no longer copies (switch step 13)

- **What:** lean-runtime pinned at `1d5d4d3` (main: semantics-4, 33420fc;
  io-fixes-1, 374f5b3; fixes-12, 1d5d4d3). The crate fixes LB-36
  (`Float.scaleB` by an `Int` outside the C `int` range), lifts LB-37 (a
  capacity that cannot be reserved), and fixes LB-39 (a task priority cut
  to 32 bits), LB-40 to LB-44 (`IO.Process.output` with a large input,
  `getLine` after a stream error, a failed spawn's duplicated output, two
  descriptor leaks) and LB-45 (`Std.Internal.UV.System`'s ids cut to 32
  bits). Three glue changes follow:
  - `sem::array::empty_with_capacity` returns the capacity to reserve (0
    when it cannot be reserved) instead of a `Result`: `leanrt::array::
    check_capacity` returns it too, 0 also when the `mi_malloc` probe of
    the native size fails, and `with_capacity_checked` reserves it; the
    prelude's `l2r_mk_empty_with_capacity` releases a big `Nat` and gives
    the empty array
    ([../representations/arrays.md](../representations/arrays.md#a-capacity-that-cannot-be-reserved-reserves-nothing)).
    `l2r_internal_panic`'s code 4 has no caller now.
  - A task's priority is passed whole: `prioOf` is `l2r_nat_sat` (the
    value, `u64::MAX` for 2^64 or more) instead of `lean_usize_of_nat`
    (the low 64 bits), and leanrt's `register` passes it to `spawn` as it
    is and keeps a dependent's until `depend` as a `u32` saturated at
    `u32::MAX`, instead of its low 32 bits
    ([../tasks/deferral.md](../tasks/deferral.md#a-priority-is-the-whole-value-above-8-is-a-dedicated-task)).
  - None for the rest: the prelude passes `Float.scaleB`'s `Int` saturated
    to `i64`, which the new `scaleb` clamps; `sys.rs` passes the whole ids
    and priority to `io::uvsys`; the prelude routes a string position of
    2^63 or more itself, so lean-runtime's new assertion in `utf8_next`,
    `utf8_next_fast` and `utf8_prev` (a position below 2^63) holds.
- **Why:** each of these is a Lean runtime bug or limit that the crate and
  both translators do not copy (plan §10, "Runtime: Lean bugs we do not
  reproduce"). Before the step, a dependent at priority 2^32 + 1 and every
  task at 2^64 or more went to the pool (test `RtTaskPrioBig`, which
  failed before the change).
- **Tests:** leanrt's unit test `array::tests::capacities`; the new
  runtime tests `RtTaskPrioBig` (every spawner at 2^32 + 1 and 2^64 while
  the one pool worker is busy) and `RtFloatScaleBBig` (the big exponents
  of `RtFloat` and `RtSweepFloat`, moved); expectation files where
  lean2rr now differs from native: `RtAllocBigNat`, `RtAllocOverflow`,
  `RtAllocOom` (LB-37), `RtTaskPrioSync`, `RtTaskPrioBig` (LB-39),
  `RtErrnoRealpath`, `RtFifoErrnoRestore`, `RtFiles2` (LB-41),
  `RtProcessSpawn` (LB-42), `RtFloatScaleBBig` (LB-36); lean-runtime's
  rows through `rows-check.sh` (the `array/mkempty.*`, `bytesempty.*`,
  `floatsempty.*` and `float/scaleb*` rows expect the definition's
  result).
- **Where:** `runtime/leanrt/src/array.rs` (`check_capacity`,
  `capacity_slow`, `native_alloc_ok`, `with_capacity_checked`), `task.rs`
  (`Entry::prio`, `register`, `depend`); `runtime/prelude.rr` (the
  `mkEmpty` externs); `Lower/LazyGlue.lean` (`prioOf`); lean-runtime's
  `docs/lean-bugs.md`.
- **Remove only if:** never.

### leanrt is built and linked with the shared crate lean-runtime

- **What:** `scripts/l2r.py` builds lean-runtime (the git submodule
  `third_party/lean-runtime`, pinned by commit; `L2R_LEAN_RUNTIME` names
  another checkout, `L2R_LEAN_RUNTIME_FEATURES` adds features) next to
  leanrt, with leanrt's rustc and flags and the features `io`,
  `proc-title`, `startup-fds`, `sched`, `stack-overflow` and `net`
  (`LEAN_RUNTIME_FEATURES`): the pinned toolchain's cargo,
  `--offline --locked --release` from inside the checkout, against cargo's
  registry cache at the versions of its committed `Cargo.lock` (`cargo
  fetch --locked` fills the cache once; `l2r.py` says so when a crate is
  missing), rlibs and the `.rmeta` of its own stub rlib from cargo's JSON
  messages. leanrt is built with `--extern lean_runtime=...` and `-L
  dependency=` for each rlib directory; the `rustc-native` wrapper that
  rrc compiles textures with adds the same, and its text names
  lean-runtime's build (its digest: rrc's texture cache keys on the
  script's text, and cargo's rlibs are in no `--polyffi-libdir`
  directory; Reussir issue 35, a cost); the link passes lean-runtime's rlibs after
  `libleanrt.rlib` and before GMP, those of the packages its normal
  dependencies reach, in the order of its dependency graph (`cargo
  metadata`: dependents first; build-script dependencies left out; review
  RULR-04). `l2r.py` stops when the submodule's checked-out commit is not
  the staged gitlink (`git ls-files -s`), and refuses a build script that
  links native libraries.
- **Why:** the two translators share Lean's runtime behaviour in one crate
  (shared-runtime decisions O6/O7: lean2rr vendors it as a submodule built
  by its driver; Q3: it builds on both projects' nightlies without nightly
  features). Every crate that calls another is linked before it, since GNU
  ld reads each archive once. Git leaves a submodule's checkout alone when
  a checkout or pull moves its gitlink, so without the pin check the suite
  would silently test an old lean-runtime (review URL-01); the index, not
  HEAD, so that a staged new pin can be tested before it is committed.
  Dependencies' build scripts set cfgs that cannot be reproduced by hand
  safely (rustix picks its backend, nix needs `cfg_aliases`), so cargo
  builds lean-runtime (review URL-08); its rlibs carry only a metadata
  stub, hence the `.rmeta`. lean-runtime keeps no `vendor/` and no
  `.cargo/config.toml`, only its `Cargo.lock` (lean-runtime's decision
  "io-1 packaging"). The plain-rustc build of the default features (steps
  1 and 2) went with step 3, which enables `io`. `proc-title`'s ELF
  constructor is lean-runtime's: its title functions refer to it, so the
  linker keeps its object whenever they are linked (checked by the title
  tests); `startup-fds`'s too, kept by `ensure_native_descriptors` and
  `mark_end_initialization`, which every program calls.
- **Where:** `scripts/l2r.py`: `LEAN_RUNTIME_FEATURES`, `build_lean_runtime`,
  `build_lean_runtime_cargo`, `cargo_link_order`, `check_pin`,
  `lean_runtime_manifest`, `LeanRuntime`, `build_leanrt`, `rustc_wrapper`,
  `leanrt_out`, and the rrc command line in `main`;
  `tests/runtime/leanrt-unit.sh`; `tests/runtime/run.sh` (stops at once
  without lean-runtime); `runtime/leanrt/src/lib.rs`: `LEAN_VERSION` and its
  test; `runtime/README.md` ("The shared crate lean-runtime": the pin,
  worktrees, the build, how to move the pin).
- **Remove only if:** lean2rr stops using lean-runtime.
