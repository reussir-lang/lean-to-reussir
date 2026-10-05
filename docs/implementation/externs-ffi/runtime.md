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
  it); `leanrt::float::to_string` writes lean-runtime's text into a 320-byte
  stack buffer (the longest `%f` of a double is 317 bytes; a longer text
  would go to the heap); `leanrt::string::utf8_count`, the count cached
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

### Huge array sizes panic with Lean's message for each allocator and size

- **What:** The sizes are lean-runtime's rules (`sem::array`): an
  allocation of more than 2^24 elements checks what Lean's allocation would
  do (`leanrt::array::check_alloc`: `sem::array::alloc_bytes`, where
  `24 + elem * n` overflowing is `INTERNAL PANIC: integer overflow in
  runtime computation` and a size above `isize::MAX` `out of memory`; then
  a `mi_malloc` of that size failing is `out of memory`). Where the size is
  a `Nat`, a big one (2^63 or more) depends on the allocator, as in
  `lean.h` and `object.cpp`:
  - `Array.replicate` (`lean_mk_array`, and lean2rr's `Array Nat`/`Array
    Int` versions `lean_mk_natarr`/`lean_mk_intarr`) takes any `n` below
    2^64 as the size (`l2r_replicate_len`, `sem::array::replicate_len`),
    so 2^63 … 2^64 − 1 overflow, and 2^64 or more is `out of memory`;
  - `Array.mkEmpty`/`emptyWithCapacity`, `ByteArray.emptyWithCapacity` and
    `FloatArray.emptyWithCapacity` (`lean_mk_empty_*`, inline in `lean.h`)
    are `out of memory` for every big `Nat` (`sem::array::
    empty_with_capacity`: the prelude's tag test, then code 4 of
    `l2r_internal_panic`, lean-runtime's `InternalPanic::OutOfMemory`; a
    small capacity is checked by `leanrt::array::check_capacity`).
  For small sizes the two agree: with 8-byte elements, 2^61 − 3 and up
  overflow, 2^61 − 4 is `out of memory`.
- **Why:** `replicate` took the `out of memory` path for every big `Nat`,
  where Lean overflows below 2^64 (cross-test XT-5, the `panics` fixture's
  row `array_replicate_nonscalar`; test `RtAllocBigNat`, which runs every
  allocator at the sizes around each boundary; `RtAllocOverflow`; and
  lean-runtime's `array/replicate.*`, `array/mkempty.*` rows through
  `rows-check.sh`). The capacity's inline tag test and its panic call keep
  the shape of the inline code at every `mkEmpty` (the panic does not
  rejoin it).
- **Where:** `runtime/prelude.rr`: `lean_mk_array`,
  `l2r_mk_empty_with_capacity`, `l2r_replicate_len`, `l2r_internal_panic`;
  the generated `lean_mk_{nat,int}arr` and
  `lean_mk_empty_{nat,int}arr_with_capacity` (`runtime/gen_tagarr.py`);
  `runtime/leanrt/src/array.rs`: `check_alloc`, `check_capacity`,
  `check_alloc_slow`, `with_capacity_checked`, `replicate`;
  `runtime/leanrt/src/tagvec.rs`: `with_capacity`, `replicate_word`;
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
  (`leanrt::panic_text`: the message, then `backtrace:` and lean-runtime's
  `NO_BACKTRACE` line unless `LEAN_BACKTRACE=0`, for Lean's current stderr
  stream; under `LEAN_ABORT_ON_PANIC`, to descriptor 2 after flushing
  stdout, then `abort`). Internal panics print
  `sem::panic::INTERNAL_PANIC_PREFIX` and the message of an
  `InternalPanic` (`leanrt::lean_internal_panic`; lean2rr's own invariant
  failures keep their own texts, `leanrt::internal_panic`) and end as
  `sem::panic::internal_panic_end` says; `uncaught exception: ` and the
  stack-overflow text are lean-runtime's constants; the index-out-of-bounds
  message is `sem::array::INDEX_OUT_OF_BOUNDS`. `panic_text` and
  `lean_internal_panic` are `extern "C"`.
- **Why:** One runtime for both translators; lean-runtime's panic rows
  (`rows-check.sh`) check them. `extern "C"` (no unwinding): the prelude's
  texture is now one call, which LLVM inlines into the panicking code; a
  Rust function there would add a landing pad and change the caller's
  code (seen in Sieve's `main`: different registers and blocks), where the
  old texture was a call to it.
- **Where:** `runtime/leanrt/src/lib.rs`: `panic_settings`, `panic_lines`,
  `panic_text`, `lean_internal_panic`, `internal_panic`,
  `uncaught_exception`, `promise_dropped`, `lean_panic`; lean-runtime's
  stack-overflow report (`sched::install_stack_overflow_handler`);
  `runtime/prelude.rr`: `l2r_internal_panic`,
  `l2r_panic_text`, `l2r_panic_code_text`.
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
    `fs::Sink`, which stops (`ByteSink::stopped`, so lean-runtime stops
    reading) and ends the process with `INTERNAL PANIC: out of memory` once
    the crate has returned (AR-5).
  - `IO.Process.output` is one primitive, `l2r_proc_output` (lean-runtime's
    `io::process::output`), with `l2r_proc_output_str`; lean2rr's
    generated drain, UTF-8 checks and `wait` are gone (`Lower/Process.lean`,
    `processOutputBody`). The `Child` operations find lean-runtime's
    process object by pid (`proc::CHILDREN`) until the child is reaped
    (`wait`, or a `tryWait` that sees it exit); a reaped child's pid gets
    the system call itself, as natively: `waitpid` (`ECHILD`), `kill` or
    `killpg` (`ESRCH`) (review RST3-04; test `RtProcessReaped`). A child
    lean-runtime models because no stand-in could be started keeps its
    standard input's read end until it is reaped (lean-runtime's model of a
    stdin that takes a pipe's capacity, then fails with `EPIPE`); natively
    the failed child closes it when it exits.
  - The shim's `Std.Internal.UV.System` functions get lean-runtime's
    errors as libuv codes (`sys::uv_code`: lean-runtime decodes them with
    `decode_uv_error(code, name)`, which keeps `-code`), and build the same
    `IO.Error` as before; `setProcessTitle` now reports a libuv error
    (`lean_shim_sys_title_set` returns it).
  - Startup: `rt`'s ELF constructor calls `io::startup::open_native_descriptors`
    (on failure `fail_as_native`: LB-30, LB-31); `l2r_set_initializing(false)`
    is `mark_end_initialization`; `main`'s return (`l2r_exit`,
    `io::main_exit`) and an uncaught error call `io::exit::after_main`
    first; every normal end calls `io::exit::exit`; an uncaught error's
    text is `io::exit::show_error` (three writes, as natively).
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
  `rt.rs` (`startup_descriptors`, `set_initializing`);
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
  start on `main`'s thread at the first task (`start_with`), `finish`
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

- **What:** `lean_system_platform_target` returns
  `leanrt::rt::PLATFORM_TARGET`, chosen by `cfg` for the target leanrt is
  compiled for: `aarch64-unknown-linux-gnu` or `x86_64-unknown-linux-gnu`,
  the triples the native Lean toolchains for those hosts report
  (`lean --version`). Any other target is a `compile_error!` naming what
  to do. The prelude's other platform answers are constants that rely on
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
- **Where:** `runtime/leanrt/src/rt.rs`: `PLATFORM_TARGET`;
  `runtime/prelude.rr`: `lean_system_platform_target`,
  `l2r_platform_target`, `lean_system_platform_windows`/`osx`/`linux`/
  `emscripten`, `lean_system_platform_nbits`.
- **Remove only if:** never; extend `PLATFORM_TARGET` (and review the
  constants) when leanrt gains a target.

### The version and git hash are the pinned toolchain's constants

- **What:** `Lean.githash` (`lean_get_githash`: the toolchain's commit),
  `Lean.version.major/minor/patch/isRelease/specialDesc` (so
  `Lean.versionString` and `Lean.toolchain`) and
  `Lean.Internal.isStage0/hasLLVMBackend` are prelude constants of the
  toolchain lean2rr is built with, v4.34.0 (`lean2rr/lean-toolchain`).
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

### leanrt is built and linked with the shared crate lean-runtime

- **What:** `scripts/l2r.py` builds lean-runtime (the git submodule
  `third_party/lean-runtime`, pinned by commit; `L2R_LEAN_RUNTIME` names
  another checkout, `L2R_LEAN_RUNTIME_FEATURES` adds features) next to
  leanrt, with leanrt's rustc and flags and the features `io` and
  `proc-title` (`LEAN_RUNTIME_FEATURES`): the pinned toolchain's cargo,
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
  tests).
- **Where:** `scripts/l2r.py`: `LEAN_RUNTIME_FEATURES`, `build_lean_runtime`,
  `build_lean_runtime_cargo`, `cargo_link_order`, `check_pin`,
  `lean_runtime_manifest`, `LeanRuntime`, `build_leanrt`, `rustc_wrapper`,
  `leanrt_out`, and the rrc command line in `main`;
  `tests/runtime/leanrt-unit.sh`; `tests/runtime/run.sh` (stops at once
  without lean-runtime); `runtime/leanrt/src/lib.rs`: `LEAN_VERSION` and its
  test; `runtime/README.md` ("The shared crate lean-runtime": the pin,
  worktrees, the build, how to move the pin).
- **Remove only if:** lean2rr stops using lean-runtime.
