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
  (aarch64 Linux, glibc 2.39). Those ports exist only on aarch64 Linux with
  glibc; on any other target their wrappers end the program with
  `INTERNAL PANIC: no lean-runtime port of <name> for this target yet`
  when called, so every other program builds and runs there (the prelude's
  textures are all compiled for every program).
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
  stack; review RULR-01). The run-time panic elsewhere keeps x86-64 and
  other targets building until lean-runtime adds their ports (its next libm
  batch, x86-64 glibc first; review RULR-02). Cost: one more call than
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
  `sem::libm` directly; the fallback panics go when lean-runtime has ports
  for every target lean2rr builds for. Check `RtFloatLoopStack` and
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
- **Why:** One runtime for both translators. Checked: lean-runtime's 1666
  rows through a lean2rr build of its row oracle (`rows-check.sh`), the
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

### A child's `null` stream is `/dev/null` opened by the parent

- **What:** For each `null` stream of `IO.Process.spawn` (so also
  `IO.Process.output`'s stdin without input), `proc::spawn` opens
  `/dev/null` in the parent (read-only for stdin, write-only otherwise)
  with `O_CLOEXEC`, after the pipes and before `fork`; the child `dup2`s
  it onto 0, 1 or 2 (where it got that very number, because the
  descriptor was closed in the parent, the child clears close-on-exec with
  `fcntl` instead), and the parent closes its copies after the fork. A
  failed open (`EMFILE`) is the spawn's error, recorded as
  `decode_io_error(errno, nullptr)` like a failed `pipe2`, and the pipes
  and `/dev/null` descriptors made so far are closed. Everything else
  follows `process.cpp`, including its leak of the pipes when a later
  `pipe2` or the `fork` fails.
- **Why:** Natively the forked child opens `/dev/null` without
  close-on-exec and never closes it after `dup2`, so the program inherits
  one more descriptor per `null` stream (LB-15), and it ignores a failed
  open, so `dup2(-1, n)` fails and the program runs on the parent's own
  descriptor n: a `null` stdout writes on the parent's standard output, a
  `null` stdin reads the parent's input (LB-17). Both are judged Lean
  runtime bugs in lean-runtime's
  [docs/lean-bugs.md](https://github.com/QueClr/lean-runtime-rs/blob/main/docs/lean-bugs.md),
  not reproduced (plan §10). The open has to be the parent's for its
  failure to be the spawn's error. Opening after the pipes keeps the
  pipes' descriptor numbers native's, and the parent's descriptors after
  the spawn are native's. One consequence: a spawn in which some `null`
  stream follows a piped one needs exactly one more free descriptor than
  natively (one in all, however many such streams), since the forked
  child has closed that pipe's other end by the time it opens `/dev/null`,
  where the parent holds both ends (stdout piped and stderr `null` with two
  free descriptors: natively the spawn succeeds, here it fails with
  `EMFILE`); any other spawn needs as many as natively. Deferring the
  open to the child after an `EMFILE` would close the gap at the cost of a
  second path (lean-runtime has the same property); not worth it for a
  process out of descriptors (review RLB-01). Nothing natively corresponds
  to the failed open, so it leaks nothing. Tests `RtProcessNullFd` (the
  child lists its descriptors; numbers dropped, 0-2 by kind and access
  mode, those above 2 compared with a child that has no `null` stream) and
  `RtProcessNullOpenFails` (under `ulimit -n 64`, the handles kept open to
  the end; then two, three and again two free descriptors, counted before
  and after each spawn), with expectation files
  `NAME.native.out`/`NAME.l2r.out`.
- **Where:** `runtime/leanrt/src/proc.rs`: `spawn` (`nulls`), `close_all`;
  plan §10, "Runtime: Lean bugs we do not reproduce".
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
  leanrt, with leanrt's rustc and flags. Without dependencies: plain rustc,
  `liblean_runtime.rlib`, the enabled features as `--cfg`, cached by a hash
  of the manifest and of the files its dep-info lists. With dependencies or
  a build script: the pinned toolchain's cargo, `--offline --locked
  --release` from inside the checkout, against cargo's registry cache at
  the versions of its committed `Cargo.lock` (`cargo fetch --locked` fills
  the cache once; `l2r.py` says so when a crate is missing), rlibs and the
  `.rmeta` of its own stub rlib from cargo's JSON messages. leanrt
  is built with `--extern lean_runtime=...` and `-L dependency=` for each
  rlib directory; the `rustc-native` wrapper that rrc compiles textures
  with adds the same; the link passes lean-runtime's rlibs after
  `libleanrt.rlib` and before GMP, those of the packages its normal
  dependencies reach, in the order of its dependency graph (`cargo
  metadata`: dependents first; build-script dependencies left out; review
  RULR-04). `l2r.py` stops when
  the submodule's checked-out commit is not the staged gitlink (`git
  ls-files -s`), and refuses what plain rustc would get wrong (a `[lints]`
  table, a workspace edition) and a build script that links native
  libraries.
- **Why:** the two translators share Lean's runtime behaviour in one crate
  (shared-runtime decisions O6/O7: lean2rr vendors it as a submodule built
  by its driver; Q3: it builds on both projects' nightlies without nightly
  features; O2: `#![forbid(unsafe_code)]` in the default build). Not capping
  its lints keeps `forbid(unsafe_code)` an error. Every crate that calls
  another is linked before it, since GNU ld reads each archive once. Git
  leaves a submodule's checkout alone when a checkout or pull moves its
  gitlink, so without the pin check the suite would silently test an old
  lean-runtime (review URL-01); the index, not HEAD, so that a staged new
  pin can be tested before it is committed. Dependencies' build scripts set
  cfgs that cannot be reproduced by hand safely (rustix picks its backend,
  nix needs `cfg_aliases`), so cargo builds lean-runtime once it has any
  (review URL-08); its rlibs carry only a metadata stub, hence the `.rmeta`.
  lean-runtime keeps no `vendor/` and no `.cargo/config.toml`, only its
  `Cargo.lock` (lean-runtime's decision "io-1 packaging").
  Checked with lean-runtime's io-1 branch at a43b009 (rustix and nix,
  Cargo.lock, no vendor/) and feature `io`: built offline from the registry
  cache, nothing written in the checkout, seven dependency rlibs linked, the
  leanrt unit tests and seven runtime tests pass; with an empty cargo home
  the build stops with the `cargo fetch --locked` hint.
- **Where:** `scripts/l2r.py`: `build_lean_runtime`,
  `build_lean_runtime_rustc`, `build_lean_runtime_cargo`, `check_pin`,
  `lean_runtime_manifest`, `needs_cargo`, `lean_runtime_features`,
  `LeanRuntime`, `build_leanrt`, `rustc_wrapper`, `leanrt_out`, and the rrc
  command line in `main`; `tests/runtime/leanrt-unit.sh`;
  `tests/runtime/run.sh` (stops at once without lean-runtime);
  `runtime/leanrt/src/lib.rs`: `LEAN_VERSION` and its test;
  `runtime/README.md` ("The shared crate lean-runtime": the pin, worktrees,
  the two builds, how to move the pin).
- **Remove only if:** lean2rr stops using lean-runtime. The plain rustc
  build can go when lean-runtime always has dependencies.
