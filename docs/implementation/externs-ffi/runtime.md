# Single externs in the runtime

Special cases inside the runtime's implementation of particular externs.
Paths are relative to the repository root.

### libm functions call glibc's, looked up in libm.so.6, opaquely

- **What:** The prelude's libm functions (the extern symbols of `Float`'s
  and `Float32`'s `sin` … `atanh`, `exp`, `exp2`, `log`, `log2`, `log10`,
  `pow`, `atan2`, `cbrt`, and their `f` versions) call
  `leanrt::float::libm::<name>`, which calls the C library's function
  through a pointer: `dlsym` on libm.so.6 opened explicitly, looked up once
  per function and cached (`resolve`). If libm.so.6 cannot be opened, the
  global scope (`dlsym(RTLD_DEFAULT, ..)`) is tried; with no C library
  function at all, the same name declared `extern "C"` is called with its
  operands passed through `black_box`. The exact operations (`sqrt`,
  `ceil`, `floor`, `round`, `fabs`) stay LLVM intrinsics.
- **Why:** Natively these externs are glibc's functions, run at run time
  even on a literal operand (a closed term is in a once-cell that clang
  cannot see into, and `lean_float_of_bits` is a runtime function).
  - Opacity. LLVM evaluates a libm call whose operand it knows (a literal,
    or a value forwarded through an inlined reference) and rewrites `pow`
    with a constant operand, and glibc's results differ in the last bit
    from what LLVM puts there: an `f32` function is folded by evaluating
    the `f64` one and rounding (`cosf`, `sinf`, `logf`, … , cross-test
    XT-4, the `float32` fixture's literal rows); `exp2` is folded through the host's
    `pow(2, x)` (`exp2(35.74477454358792)`, found by another Lean translator's review); `pow(x, 0.5)`
    becomes `sqrt`, `pow(x, 2.0)` `x * x`, `pow(x, -1.0)` `1 / x`,
    `pow(2.0, y)` `exp2`, `pow(10.0, y)` `exp10`, for `pow` and `powf`
    (cross-test XT-3, fixture A720). The prelude used LLVM's intrinsics
    (`llvm.pow`, `llvm.cos.f32`, …) for most of them, and plain `extern
    "C"` calls for the others, which LLVM recognizes and folds by name
    too (`logf`). An indirect call through a pointer read at run time
    cannot be folded or rewritten. Folding an `f64` function other than
    `exp2` with the host's libm gives glibc's result on the build machine
    (a sweep of 100 random literal operands per function found differences
    only in `f32` functions; another translator's sweep of 800 found only `exp2`), but
    a build machine with another C library would not.
  - glibc's function. A direct `extern "C"` declaration does not reliably
    reach glibc: Rust's `compiler_builtins`, linked into every executable
    ahead of libm, defines its own `cbrt` (a port of CORE-MATH's correctly
    rounded one) and `cbrtf` (FreeBSD's) on Linux, and the static link
    binds every reference named `cbrt` to those. They differ from glibc's
    by 1-2 ulps on about half the doubles (cbrt 27.0 is 3.0 there and
    3.0000000000000004 in glibc) and on about one float in ten.
    `compiler_builtins` defines no other function of this list today
    (checked with `nm` on the pinned toolchain), but Rust keeps moving
    float functions into `core`. The global scope holds libm only while the
    executable imports some libm function; a Rust program without one finds
    no `cbrt` there (fix-r9-misc).
  - Tests: `tests/runtime/RtFloatLibmFold.lean` (each function on a
    literal operand and on the same operand from the command line, inputs
    where the folded or rewritten value differs from glibc's; 31 of its 42
    lines differed before), `RtFloatCbrt.lean`; leanrt's unit tests
    `float::libm::tests` (`tests/runtime/leanrt-unit.sh`, a binary without
    libm imports).
  - lean2rr executables are dynamic PIEs, and libm.so.6 is one of their
    load-time dependencies. A fully static build would have no libm.so.6
    to open: the fallback then calls the `extern "C"` names, which bind to
    Rust's `cbrt`/`cbrtf`, so if static linking is ever added, it must link
    glibc's `cbrt` some other way.
- **Where:** `runtime/leanrt/src/float.rs`: `libm` (`resolve`, the
  `glibc!` functions, the fallback declarations in `libm::c`);
  `runtime/prelude.rr`: the libm functions after `l2r_float32_scaleb_big`.
- **Remove only if:** LLVM stops folding and rewriting libm calls (it will
  not: it assumes the C standard's functions), or the native oracle starts
  folding them too. The `dlsym` lookup in particular is needed while
  `compiler_builtins` defines `cbrt`/`cbrtf` on Linux.

### Huge array sizes panic with Lean's message for each allocator and size

- **What:** An allocation whose size is not a small number checks what
  Lean's allocation would do (`leanrt::array::check_alloc`, for more than
  2^24 elements): `24 + elem * n` overflowing is `INTERNAL PANIC: integer
  overflow in runtime computation`, a `mi_malloc` of that size failing is
  `out of memory`. Where the size is a `Nat`, a big one (2^63 or more)
  depends on the allocator, as in `lean.h` and `object.cpp`:
  - `Array.replicate` (`lean_mk_array`, and lean2rr's `Array Nat`/`Array
    Int` versions `lean_mk_natarr`/`lean_mk_intarr`) takes any `n` below
    2^64 as the size (`l2r_nat_to_size_t`), so 2^63 … 2^64 − 1 overflow,
    and 2^64 or more is `out of memory`;
  - `Array.mkEmpty`/`emptyWithCapacity`, `ByteArray.emptyWithCapacity` and
    `FloatArray.emptyWithCapacity` (`lean_mk_empty_*`, inline in `lean.h`)
    are `out of memory` for every big `Nat`
    (`l2r_mk_empty_with_capacity`, `lean_mk_empty_natarr_with_capacity`).
  For small sizes the two agree: with 8-byte elements, 2^61 − 3 and up
  overflow, 2^61 − 4 is `out of memory`.
- **Why:** `replicate` took the `out of memory` path for every big `Nat`,
  where Lean overflows below 2^64 (cross-test XT-5, the `panics` fixture's
  row `array_replicate_nonscalar`; test `RtAllocBigNat`, which runs every
  allocator at the sizes around each boundary; `RtAllocOverflow`).
- **Where:** `runtime/prelude.rr`: `lean_mk_array`,
  `l2r_mk_empty_with_capacity`, `l2r_nat_to_size_t`; the generated
  `lean_mk_{nat,int}arr` (`runtime/gen_tagarr.py`);
  `runtime/leanrt/src/array.rs`: `check_alloc`, `check_alloc_slow`,
  `replicate`; `runtime/leanrt/src/nat.rs`: `nat_to_size_t`.
- **Remove only if:** never (the messages are observable).

### A large read right after output writes the pending output first

- **What:** In the `FILE` model, a read of at least one buffer (the direct
  path of `xsgetn`) right after output on the same handle first writes the
  pending output, as `fflush` would; if that write fails, the read fails
  with its error. A failed seek back over read-ahead before the write
  (`ESPIPE`: a FIFO opened `readWrite` and read ahead) is no failed write:
  then, as glibc's direct read does, the pending output and the read-ahead
  are dropped and the read goes on (`new_do_write` sets `seek_failed`), with
  `errno` restored to its value before the attempt, since native's direct
  read makes no seek and a later error report (`getLine` on a handle with
  its error indicator set) reads `errno` (review RXT-06).
  Then it reads from the cursor (a write-only handle then fails with EBADF,
  as natively). Everything else follows glibc.
- **Why:** glibc's `_IO_file_xsgetn` resets the put area there and drops
  the pending output (C11 7.21.5.3p7 makes output directly followed by
  input undefined): written data never reaches the file. Judged a Lean
  runtime bug, LB-02 in lean-runtime's
  [docs/lean-bugs.md](https://github.com/QueClr/lean-runtime-rs/blob/main/docs/lean-bugs.md); the owner's ruling is not
  to reproduce it. A first version treated every failure of the write-out
  as a failed write, so on a FIFO opened `readWrite` the read, the next
  read and the flush all failed with `invalid seek` where native reads on
  (review RXT-01, the same fix as lean-runtime io-1's af6ecf2). Tests
  `RtReadAfterWrite`, `RtStdioStdoutRead` (expectation files
  `NAME.native.out`/`NAME.l2r.out`), `RtFifoReadAfterWrite` (the FIFO, the
  same as native), `RtFifoErrnoRestore` (the `errno` a later report sees); leanrt's differential test of the model against glibc
  (`Glibc::read_lb02`) flushes glibc's `FILE` before a read that takes the
  direct path with output pending, which makes glibc's behaviour defined
  and the model's (a failed `fflush` with `ESPIPE` reads on, any other
  ends the read), and has a FIFO case
  (`differential_against_glibc_fifo_read_write`).
- **Where:** `runtime/leanrt/src/cfile.rs`: `xsgetn`, `new_do_write`
  (`seek_failed`); `runtime/leanrt/src/cfile_tests.rs`: `Glibc::read_lb02`,
  `run_case`, `fifo_case`; plan §10, "Runtime: Lean bugs we do not
  reproduce".
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
  x86-64 (signal structures, the glibc `FILE` model, `coro`'s stack
  switching), hence the error elsewhere instead of a guess. Test
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
  `lean_version_get_*`, `lean_internal_*`; test `RtPlatform`.
- **Remove only if:** never. Update them with every toolchain change;
  `RtPlatform` fails otherwise.
