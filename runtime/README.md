# lean2rr runtime

The runtime has these parts:

- `prelude.rr` — Reussir source that lean2rr prepends to every generated
  program. It defines the runtime types and one function per Lean extern
  (`lean_xxx` for the extern whose C symbol is `lean_xxx`), plus `l2r_*`
  primitives for lean2rr-generated glue.
- `leanrt/` — a Rust crate (rlib) linked into every program. The prelude's
  `#[ffi(import)]` textures call into it. It holds lean2rr's
  representations (strings, arrays, tagged arrays, cells) and the glue
  around lean-runtime's rules and IO (files, standard streams, the file
  system, processes, `Std.Internal.UV.System`, the startup descriptors and
  the exit: `fs`, `io`, `proc`, `sys`, `rt`; tasks, promises, `Std.Sync`
  and `Std.Internal.UV`'s loop, timers, signals and sockets: `task`,
  `sched`, `sync`, `net`), the bignum code (GMP), once-cells, panics and
  the main-thread setup — and, being a single crate, the one copy of all
  global state (statics in the prelude's `extern "rust"` block would be
  duplicated per texture).
- `lean2rr/L2RShim.lean` (built with lean2rr) — Lean implementations of the
  `Std.Internal.UV` externs (timers, sockets, name resolution, signals,
  `Std.Net` addresses), `Std.Time.Timestamp.now` (over
  `l2r_shim_realtime_nanos`), the Windows-only time zone externs (their
  error elsewhere) and `ShareCommon.Object.eq`/`hash`, exported under their
  C symbols, which lean2rr compiles with the program over the
  `l2r_shim_*` primitives of lean-runtime's event loop (below).
- `third_party/lean-runtime` (a git submodule) — the crate `lean_runtime`,
  Lean's runtime behaviour shared with another Lean translator: its
  `semantics` and, with its features `io`, `proc-title`, `startup-fds`,
  `sched`, `stack-overflow` and `net`, its OS-level IO, its task scheduler (with
  `Std.Sync`, the event loop, timers and signals) and its networking.
  The rules it has are its alone: the prelude's textures (as `sem::...`)
  and `leanrt` call it and only convert lean2rr's values to its views and
  back ("The shared crate lean-runtime", below).

Semantics follow Lean 4.34's C runtime (`lean.h`, `src/runtime/*.cpp`)
exactly; comments at each function say which C function it mirrors. Inline
Reussir code is kept for single operations (wrapping arithmetic, bitwise
operations, comparisons, casts, bit copies); every rule with logic that
lean-runtime has is lean-runtime's.

Generated sections of the prelude (edit the generator, then run it):
`runtime/gen_scalars.py` (UIntN/IntN/USize/ISize: the single operations
inline, the rest textures calling `sem::uint`, `sem::sint`, `sem::float`)
and `runtime/gen_tagarr.py` (`Array Nat`/`Array Int`).

## Building and linking

`scripts/l2r.py` does everything:

1. builds the shared crate `lean_runtime` (below), then `leanrt` against
   it, both with the pinned rustc (`L2R_RUSTC`) and the same flags, into
   `runtime/leanrt/target/` (`liblean_runtime.rlib`, `libleanrt.rlib`;
   `target/rt-<hash>/` for another Reussir checkout), each cached (leanrt
   by a hash of its sources and of lean-runtime's build). rustc runs in
   the crate's directory, whatever the caller's: rustc records its working
   directory in the rlib, and rrc's texture cache (step 3) hashes the
   rlibs, so a rebuild from another directory would miss on every texture;
   built this way, a rebuild gives the same bytes;
2. runs lean2rr (`L2R_LEAN2RR`) with `--prelude runtime/prelude.rr`;
3. runs rrc (`L2R_REUSSIR`; with `--reuse-across-call` unless `l2r.py` gets
   `--no-reuse-across-call`) with
   - `--polyffi-rust-path <leanrt dir>/rustc-native`: a wrapper that
     adds `-C target-cpu=native -C target-feature=-outline-atomics`. With the
     plain rustc, textures are not inlined into Reussir code, and calls through
     the packed-argument boundary (float or `str` arguments, four or more
     parameters) leave an escaping stack slot that blocks tail-call
     elimination: loops that print floats overflow the stack. It also adds
     `--extern leanrt=<rlib>` (and `--edition 2018` when rrc gives no
     edition): the drop hooks Reussir generates for the prelude's opaque
     types are textures without the prelude's `extern crate leanrt;`, and
     the containers' Rust types are `leanrt`'s (below). And it adds
     `--extern lean_runtime=<rlib>` (and `=<rmeta>` for cargo's rlib, which
     holds only a metadata stub) with `-L dependency=<dir>` for each
     directory of lean-runtime's rlibs: rustc needs `lean_runtime` whenever
     it loads `leanrt`, and the prelude's textures call it (as `sem`).
   - `--polyffi-libdir runtime/leanrt/target` (so textures find `leanrt`
     and `lean_runtime`),
   - `--link-lib libleanrt.rlib --link-lib liblean_runtime.rlib` (then
     lean-runtime's dependencies, dependents first) `--link-lib libgmp.a`,
     in this order: GNU ld reads each archive once, so a library comes after
     the ones that call it (GMP from the Lean toolchain,
     `$(lean --print-prefix)/lib/libgmp.a`, or `L2R_GMP`),
   - and the environment variable `REUSSIR_FFI_CACHE_DIR`
     (`runtime/leanrt/target/polyffi-cache`, unless the caller sets it;
     empty turns it off): rrc compiles each of the prelude's textures with
     its own rustc run, about 470 per program and most of rrc's time, and
     with Reussir patch 0066 it keeps their bitcode there and reuses it
     (Reussir issue 35, a cost; an rrc without the patch ignores the
     variable). Its key covers the texture, the `rustc-native` script (whose
     text also names lean-runtime's build), rustc's options and every
     library in the `--polyffi-libdir` directories, so a change to leanrt or
     lean-runtime only makes new entries. Old entries are never removed:
     delete the directory to reclaim the space. rrc checks entries for
     damage, not for tampering: the directory must be one only you can
     write.

### The shared crate lean-runtime

The lean-runtime crate (repo [lean-runtime-rs](https://github.com/QueClr/lean-runtime-rs)) is Lean 4.34.0's
runtime behaviour as one Rust crate, shared with another translator (of
Lean to safe Rust): the parts that do not depend on how a translator
represents values (semantics on byte views and plain data, then OS-level IO
and the task scheduler). lean2rr keeps its representations, memory protocol
and hot paths in `leanrt` and the prelude, which call lean-runtime for the
rest.

- **The pin.** lean-runtime is the git submodule `third_party/lean-runtime`,
  pinned at a commit of its `main` (now `471f458`). Clone lean2rr with
  `git clone --recurse-submodules`, or run `git submodule update --init
  third_party/lean-runtime` in a checkout, and again after a checkout,
  merge or pull that moves the pin: git does not update a submodule on its
  own (`git config submodule.recurse true` makes it). `l2r.py` stops with
  the hint when the submodule is empty, and when its checked-out commit is
  not the pinned one (the gitlink in the index, `git ls-files -s
  third_party/lean-runtime`).
- **Worktrees.** Each `git worktree add` gets its own copy of the
  submodule: run `git submodule update --init` in the new worktree (a clone
  from GitHub; `--reference <main checkout>/.git/modules/third_party/lean-runtime`
  avoids the network once the main checkout has it). Git refuses to remove
  a worktree that contains a submodule: check that `git -C WT status
  --porcelain` and `git -C WT/third_party/lean-runtime status --porcelain`
  print nothing, then `git worktree remove --force WT`. Never run `git
  submodule deinit` in a worktree: it deletes the submodule's entries from
  the shared `.git/config`, for the main checkout and every worktree.
- **The build.** lean2rr enables lean-runtime's features `io` (its
  OS-level IO, over rustix, nix and io-uring), `proc-title` (the process
  title in the arguments' memory: a native quirk written with `unsafe`,
  `UNSAFE.md` in the submodule), `startup-fds` (native Lean's startup
  descriptors opened by the crate's own ELF constructor before Rust's
  runtime starts: another native quirk with `unsafe`), `sched` (the task
  scheduler over
  corosensei, its event loop over rustix's epoll, signal watchers over
  signal-hook), `stack-overflow` (Lean's stack-overflow report: another
  native quirk with `unsafe`; named on its own, as lean-runtime's newer
  branches no longer turn it on with `sched`) and `net` (sockets, name
  resolution over dns-lookup). The dependencies' build scripts need cargo, so the
  pinned toolchain's cargo builds it: `cargo build --offline --locked
  --release --lib --features io,proc-title,startup-fds,sched,stack-overflow,net[,...]` from inside the
  checkout, from the crates in cargo's registry cache
  (`~/.cargo/registry`) at the versions its committed `Cargo.lock` names
  (so nothing is written in the checkout; lean-runtime has no `vendor/`),
  with `RUSTC` and `RUSTFLAGS` set to leanrt's rustc and flags (`-C
  opt-level=3` comes from cargo's release profile; the native-CPU flags
  above, `L2R_LEANRT_RUSTFLAGS`), and a target directory under leanrt's.
  Fill the cache once with `cargo fetch --locked` in the lean-runtime
  checkout (the pinned toolchain's cargo); `l2r.py` says so when a crate is
  missing, and every build after it is offline. The rlibs come from
  cargo's JSON messages; linked are those of the packages lean-runtime's
  normal dependencies reach on this host (`cargo metadata
  --filter-platform`; a build script's own dependencies, such as
  `cfg_aliases`, are not), each before the packages it depends on; the
  environment's `CARGO_ENCODED_RUSTFLAGS`, `CARGO_BUILD_RUSTFLAGS` and
  `CARGO_TARGET_*_RUSTFLAGS` are removed, since they would override
  `RUSTFLAGS`. Cargo's fingerprints are the cache. Build scripts run as
  cargo runs them; one that links native libraries is refused (`l2r.py`
  does not pass those on yet). leanrt itself stays a plain rustc build.
  `proc-title`'s ELF constructor is lean-runtime's own: the title
  functions refer to it, so the linker keeps its object in every program
  that calls them (checked by the title tests, `RtSystem` and
  lean-runtime's `uvsys/process_title`, `title_cmdline`). So is
  `startup-fds`'s: `ensure_native_descriptors` and
  `mark_end_initialization`, which every program calls, refer to it
  (checked by the descriptor tests, `RtFdLimit`, `RtFdStartupNoUring`,
  `RtStartupFdExhausted`, `RtClosedStreams`).
- **Trying another lean-runtime.** `L2R_LEAN_RUNTIME=<checkout>` builds
  that checkout instead of the submodule (its checked-out commit is not
  compared with the pin), in its own directory (`target/.../lr-<hash>/`),
  e.g. a lean-runtime branch whose merge waits for lean2rr's suite;
  `L2R_LEAN_RUNTIME_FEATURES=...` adds features to lean2rr's
  (`scripts/l2r.py`: `LEAN_RUNTIME_BASE_FEATURES`). `tests/runtime/leanrt-unit.sh`
  and the test runners (through `l2r.py`) follow both.
- **Moving the pin.** Each project moves its pin only after its own suite
  passes on the new commit:
  1. `git -C third_party/lean-runtime fetch origin` and `git -C
     third_party/lean-runtime checkout <commit>` (a commit on lean-runtime's
     `main`), then stage it: `git add third_party/lean-runtime` (`l2r.py`
     builds the staged pin);
  2. run lean2rr's suite on it: `tests/runtime/leanrt-unit.sh`,
     `tests/runtime/rows-check.sh` (lean-runtime's own rows through
     lean2rr), `tests/runtime/ffi-inline-check.sh` (lean-runtime's
     functions leave no stack slot in Reussir code),
     `tests/runtime/wait-inline-check.sh` (the fast paths of its wait
     cores stay inline in an executable's loops), the runtime tests
     (`tests/runtime/run.sh`),
     `tests/runtime/nat-alloc-check.sh`, `tests/env/run.sh`, the classic
     corpus (`tests/oracle.py check`, with the optional passes on and off)
     and `tests/reussir-benchmark/run.sh`;
  3. commit the new pin on its own, naming the old and new commits and the
     suite's results.
- **What lean2rr uses.** `LEAN_VERSION` (re-exported as
  `leanrt::LEAN_VERSION`; the unit test
  `tests::lean_runtime_version_is_the_preludes` checks it is the version
  the prelude's `lean_version_get_*` give) and, from its `semantics`
  module:
  - `hash`: `String.hash`, `ByteArray.hash`, `String.Slice.hash`, `mixHash`;
  - `string`: `get`, `get?`, `get!` (with its panic text), `get'`, `next`,
    `next'`, `prev`, `atEnd`, `isValid`, `extract` and `extract_fast`
    (lean-runtime gives the byte range, `leanrt::string` makes the string),
    `getUTF8Byte`, `memcmp`, `decLt`, `compare`, the default character,
    the character count a string caches when it is made (`utf8_strlen`;
    `String.length` reads the cached count), the UTF-8 encoding of a
    character (`push_unicode_scalar`, inline in `String.push`'s and
    `String.set`'s slow paths) and the lossy decoding of bytes
    (`lossy_utf8`, `lean_mk_string_lossy_recover`). A big `Nat` position is
    passed as `u64::MAX` (`l2r_pos_of_nat`); `next` takes a position below
    2^63 and may answer 2^63, which becomes a big `Nat`;
  - `float`, `float32`: `toString` (written into a stack buffer by
    `leanrt::float`), `ofBits`/`toBits`, `frExp`, `scaleB` (a big `Int` is
    passed as `i64::MIN`/`MAX` by its sign, `l2r_int_sat_i64`), `isNaN`,
    `isInf`, `isFinite`, the saturating conversions to `UIntN`/`IntN`;
  - `uint`, `sint`: `div`, `mod`, `shiftLeft`, `shiftRight`, `log2`,
    `IntN.abs`;
  - `libm`: every `Float`/`Float32` libm extern, `cbrt`, `cbrtf`, `atanh`,
    `atanhf` included (lean-runtime's ports of glibc's, the same algorithm
    on every target). Those four and the ones that hide their operands with
    `black_box` are called out of line (`leanrt::float::libm_call`, one call
    more than native Lean's direct libm call), so that a Lean loop calling
    them stays a loop;
  - `nat`, `int`, over `bignum`'s traits: every `Nat`/`Int` slow path
    (`leanrt::nat`, below: the prelude's inline small cases stay lean2rr's)
    is lean-runtime's rule on its words, with `leanrt::big`'s numbers as
    `BigNat`/`BigInt` (`big::GNat`, `big::GInt`; `big::MAX_BITS`, the
    largest result, is GMP's `INT_MAX` limbs less `mpz_pow_ui`'s margin of
    5 limbs, (2^31 - 6) × 64 bits: above it the rules end with `INTERNAL
    PANIC: out of memory`, LB-05). The rules lift Lean's limits where the
    result fits (`Nat.pow` and `Nat.shiftLeft` by 2^32 or more,
    `Nat.shiftRight` of a huge value; LB-04, LB-11, LB-12);
  - `array`: the allocation sizes (`alloc_bytes`, `replicate_len`,
    `empty_with_capacity`), `copySlice`'s plan (offsets and lengths of 2^64
    or more passed saturated, `l2r_nat_sat`: LB-06), the index-out-of-bounds
    message; the bounds tests themselves stay inline comparisons;
  - `panic`: `lean_panic_fn`'s plan (`panic_fn_plan`: the lines, the
    stream, abort under `LEAN_ABORT_ON_PANIC`), the internal panics'
    messages and endings, the `uncaught exception: ` prefix, the
    stack-overflow text (`leanrt::panic_text`, `lean_internal_panic`);
  - `repr`: the decimal digits of a word (`decimal_u64_bytes`:
    `USize.repr`, `Nat.repr`, `Int.repr`; a big number's are its
    `write_decimal`, GMP's `mpz_get_str`);
  - `toolchain`: `Lean.githash`, `Lean.version.specialDesc`,
    `System.Platform.target`.

  and, from its `io` module (features `io`, `proc-title`, `startup-fds`):
  - `handle`, `cfile`: `IO.FS.Handle` and the three standard streams,
    glibc's `FILE` model behind each (buffering, read-ahead, positions, the
    sticky indicators, LB-02), the open-handle list; `leanrt::fs` keeps a
    `Handle` in an `LHandle` box (closed with the box's last reference, in
    Lean's order inside a container's free), `leanrt::io` calls the
    standard streams' handles. A read goes straight into the `ByteArray`'s
    own block (`Handle::read_uninit` through `array::bytes_filled`);
    `getLine` appends to a `Vec<u8>` (below, "Sinks");
  - `error`: `IO.Error` as data (`IoError`), decoded from `errno`s and
    libuv codes, with its accessors (`os_code`, `file_name`, `details`)
    and its builder number (`builder_index`, the order of
    `IO_ERROR_BUILDERS`, which lean2rr's `ioErrorBuilderSyms` and the
    shim's `ioErrorOf` follow: unit test
    `tests::io_error_builders_are_lean_runtimes`); `leanrt::fs` keeps the
    last one in its slot and gives its builder number, code, file name and
    details to the generated glue (below);
  - `fs`, `temp`, `env`: the file system, temporary files, `IO.getEnv`,
    `IO.appPath`, the pid, `IO.getTID` (`get_tid`: `gettid`, plus the
    number of the OS thread the code natively runs on, `sched::tid_offset`),
    random bytes, the monotonic
    clock (`IO.monoMsNow`'s `mono_ms_now` too);
  - `process`: `IO.Process.spawn` (over `posix_spawn`, the forked child's
    steps reproduced; LB-15, LB-17), `wait`, `tryWait`, `kill` (LB-14),
    `IO.Process.output` with its `StoppingSink`s (`leanrt::proc` keeps each
    child's process object by pid until it is reaped; a reaped child's pid
    gets lean-runtime's object for it, `ChildProcess::from_pid`);
  - `uvsys`: `Std.Internal.UV.System`'s queries (`leanrt::sys`, for the
    shim), the process title written into the arguments' memory
    (`proc-title`);
  - `time`, `debug`: `timeit`'s line, `Std.Time.Timestamp.now`'s clock
    (`current_time_nanos`), `Std.Time.Database.Windows`'s errors off
    Windows, `allocprof`'s text (`allocprof_text`), `dbgTraceIfShared`'s
    line (`shared_rc_line`);
  - `startup`: native Lean's startup descriptors, which lean-runtime's own
    ELF constructor opens since switch step 7 (feature `startup-fds`,
    `.init_array.00101`; `leanrt::rt::run_main2` calls
    `ensure_native_descriptors`, which keeps it linked; a failure ends the
    program with lean-runtime's message: LB-30, LB-31), `main`'s thread
    (`run_main`, `main_on_thread`) and `IO.initializing`;
  - `exit`: the exit sequence (every normal end of the process, through
    `leanrt::io::exit`), `after_main` (`main`'s return and an uncaught
    error), `show_error` (an uncaught error's text).

  What stays lean2rr's: the current standard streams of `IO.setStdout` &
  co. (lean2rr's cells of its own `IO.FS.Stream` records, generated with
  the program and set aside per context and per task: `IO.println` reads
  the current stdout at every call, inline) and `forceExit` (`_exit`,
  below). Since lean2rr runs on lean-runtime's
  scheduler (`sched`), its IO cooperates: a read of an empty pipe, a write
  to a full one, `flock` and `Child.wait` let the other contexts run.

  and, from its `sched` module (features `sched`, `stack-overflow`):
  - the task manager (`spawn`, `depend`, `wait`, `wait_any`, `state`,
    `cancel`, `check_canceled`, `release`, `promise_new`, `resolve`,
    `option_get_or_block`, `start_with`, `finish`, `end_running_task`,
    `running_worker`, `await_task` (`Task.get`'s rule in a `sync` task),
    `thread_create_failed` (libc++'s abort text when `main`'s thread
    cannot be made), the yield points `effect`, `poll`, `sleep_ms`,
    `ref_read`, the publication `before_publish`), its contexts, the
    per-context and per-task hooks of `Glue`, the
    no-suspend scope (`leanrt::task`, `sched`, `refs`, `drop`, `fs`:
    below, "Thunks and tasks", "The scheduler");
  - the wait cores (wait-1), in their keyed form: a computation another
    context runs (`step_keyed`, `wait_running_keyed`, `done_keyed`: a
    `busy` thunk under its address, a constant under `(slot << 1) | 1`;
    `leanrt::sched`, `once`), the references of a program that creates
    tasks under Lean 4.35's rule (`ref_keyed`, `leanrt::refs`), and the
    resolution of a promise a free drops, put off to the free's end
    (`defer`, `Deferred`, `run_deferred`, `deferred_pending`;
    `leanrt::task`);
  - `sync`: `Std.Sync`'s mutexes and condition variable (`leanrt::sync`);
  - `uv`: `Std.Internal.UV`'s loop, timers and signal watchers
    (`leanrt::net`, for the shim);
  - Lean's stack-overflow report (`install_stack_overflow_handler`,
    `leanrt::rt`);

  and, from its `net` module (feature `net`): TCP and UDP sockets, name
  resolution and interface addresses (`leanrt::net`, for the shim); from
  `semantics::net`, the text forms of addresses.

## Representations

| Lean (mono) | Reussir | Notes |
|---|---|---|
| `Nat` | `Nat` = `leanrt::nat::LNat`, one word, declared `tagged` (Reussir patch 0050) | odd: the small value `(n << 1) \| 1`, n < 2^63; even: an owned `LBig` pointer (below) |
| `Int` | `Int` = `leanrt::nat::LInt`, likewise | odd: `lean_box((unsigned)(int)i)` for i in the `int32` range; even: an owned `LBig` pointer |
| big numbers | `LBig`, one `mi_malloc` block: count `u32`, flags `u32`, signed size `i32` (limbs in use, negative for a negative value), capacity `u32`, then the limbs | GMP `mpn` operations on the limbs, in a unique operand's block with room (grown by a carry, shrunk when a result leaves most of it unused) or a fresh one; `mpz` operations on read-only views for `pow`, `gcd`, parsing and printing; normalized (only values outside the small ranges); only behind a `Nat`/`Int` word |
| `String` | `LStr` = `leanrt::string::LStr`, a pointer to one block: count, byte size, capacity, character count (32 bytes, as Lean's header), bytes | valid UTF-8, no terminator, and the character count (Lean's `m_length`, kept by every operation: `String.length` is O(1)); copy-on-write; grows by `realloc` (below) |
| `Array α` | `RVec<E>` = `leanrt::drop::Vec<E>`, a pointer to one block: count `u32` (padded), size, capacity (24 bytes), then the elements | `E` = storage type of `α` (lean2rr boxes non-boundary types); copy-on-write, grows by `realloc`; freed without recursion (below) |
| `Array Nat`, `Array Int` | `LNatArr`, `LIntArr` = `leanrt::tagvec::TagVec` | the elements' own words, one block with Lean's 24-byte header (below) |
| `ByteArray`, `FloatArray` | `RVec<u8>`, `RVec<f64>` | `ByteArray.mk`/`data` (and `FloatArray`'s) are the identity (`Array UInt8` is `RVec<u8>` too); `String.toUTF8`/`fromUTF8` copy the bytes, as natively |
| `ST.Ref σ α` / `IO.Ref α` | a lean2rr-generated shared record `L2RRefN(Cell<E>)` around a Reussir cell (two allocations: the record and the cell); a `Nat`/`Int` reference holds the handle like any other | mutated through every alias; `take` leaves the placeholder |
| `Thunk α`, `Task α` | `LCell<S>` = `leanrt::drop::Cell<S>`, a transparent wrapper of `Rc<S>` | one mutable value, seen through every alias; `S` is a state enum lean2rr generates (below) |
| `IO.FS.Handle` | `LHandle` | shared buffered file, closed with its last reference |
| `UInt8..64`, `USize` | `u8..u64`, `u64` | |
| `Int8..64`, `ISize` | `u8..u64`, `u64` (bit patterns) | signed semantics as `lean_int8_*` etc. |
| `Char` | `u32` | |
| `Float`, `Float32` | `f64`, `f32` | |
| `Bool` | `bool` | |
| `Unit`, `PUnit`, erased | `L2RUnit` | `enum [value] L2RUnit { u }` |

Every function consumes its arguments (Reussir's convention). Strings,
arrays and big numbers are updated in place when uniquely referenced
(count 1), otherwise copied once. Textures that only read a handle
release it through `leanrt::rc_release` (any `leanrt::Release` handle:
Reussir's `Rc`, `LStr`, `TagVec`)/`array::release`, whose last-reference
drop is out of line; together with `#[inline(always)]` fast paths and
`#[cold]` slow paths this lets LLVM inline the hot textures (array
get/set/push/size, string get/next/push, the Nat helpers) into Reussir code
(checked with `rrc --emit llvm-ir`). Inlined, a read's release meets the
caller's increment, and LLVM folds the pair (the free check included,
thanks to the `old count >= 1` that Reussir's `rc.inc` asserts) as long as
no other store or call lies on a path between them. So indices that are
in bounds by a proof (`fget`, `fset`, `fswap`, and the checked variants
after their bounds test) and positions proved valid (`String.Pos.get`,
`next`) are converted by `l2r_index_of_nat`, whose impossible big case
ends the program instead of rejoining the read with refcount traffic on
the big number; a checked index (`get!`, `set!`) is taken as its word once
(`l2r_word_index_ok`), so in bounds there is no refcount traffic on it at
all.

**`Nat`/`Int`.** One word each, with Lean's exact encoding
(`leanrt::nat`): an odd word is a small value, `lean_box(n)` for a `Nat`
below 2^63 and `lean_box((unsigned)(int)i)` for an `Int` in the `int32`
range; an even word is an owned reference to a big number, one block
with a 16-byte header and the limbs inline (`leanrt::big`; native Lean's
`lean_mpz_object` keeps the limbs in a second allocation). C code written
against `lean.h` could take and return the small words unchanged; a big
number would be converted. Reussir copies and drops them as handles of an opaque type declared
`#[ffi(rust = "::leanrt::nat::LNat", tagged)]`: with Reussir patch 0050 it
counts only even words (`rc.inc` and the drop hook, `LNat`'s `Drop`, run
only when the low bit is clear). The prelude's functions take each `Nat`
argument as its word once (`l2r_nat_raw`, which then owns the reference),
compute small results inline, and call `leanrt::nat`'s slow paths
(`nat_add`, ... taking owned words, every small/big combination: each
views its words as lean-runtime's `Nat`/`Int`, runs lean-runtime's rule
and normalizes the result) for the rest; `l2r_nat_of_raw` makes a handle of a word, `l2r_nat_drop_raw`
releases one. The slow paths normalize: a `Nat` below 2^63 (an `Int` in
`int32`) is always small, so two small words are equal exactly when the
values are. A build with `L2R_LEANRT_RUSTFLAGS="--cfg leanrt_count_bigs"`
counts the big numbers made and freed and prints the counts at exit
(`tests/runtime/nat-alloc-check.sh`).

**`Array Nat`/`Array Int`.** `LNatArr`/`LIntArr` (`leanrt::tagvec`, the
`nat-arrays` pass) store the elements' words, like Lean's array object:
the handles move in and out as their words (`l2r_natarr_get` wraps the
owned word it reads, `l2r_natarr_set` stores `l2r_nat_raw(x)`). Without
the pass an `Array Nat` is an `RVec<Nat>`, one word per element in the
same layout (the generic array's block). Every
`lean_array_xxx<E>` / `l2r_array_xxx<E>` has `lean_natarr_xxx` /
`l2r_natarr_xxx` (and `intarr`) with the same arguments and element type
`Nat` (`Int`); `lean_mk_array`/`lean_mk_empty_array_with_capacity` become
`lean_mk_natarr`/`lean_mk_empty_natarr_with_capacity`. A tag vector is one
allocation laid out like Lean's array object: the count (a `u32`, padded
to a word), the size, the capacity, then the words, so a three-element
array takes 48 bytes as natively. A copy of a shared one keeps its
capacity (`lean_copy_expand_array`), so a literal `#[a, b, c]`, which
pushes onto a shared empty array of capacity 3, allocates once.

**Runtime-owned objects.** `LStr`, `TagVec` and the arrays (`RVec`,
`LRef`: `leanrt::drop::Vec`) are `leanrt` types: a `#[repr(transparent)]`
pointer to a block allocated with `mi_malloc`, whose first word is the
`u32` count. That is all Reussir needs of an opaque type (its `rc.inc`
increments the count inline, its uniqueness analysis reads it; `rc.dec`
calls the type's drop hook, a texture that drops the Rust value), so their
`Clone` and `Drop` do the counting, the drop's last reference out of line.
A unique block grows in place with `mi_realloc` (at least doubling; the
capacity is the whole block: mimalloc's size class, `mi_good_size`, for
small blocks, a power of two above 4 KiB); a fresh block's size is
rounded up to 8 bytes, the rest becoming capacity; a shared one is copied
with room for the update (a string: at least doubled, as
`lean_string_push`; an array, for a push: `lean_array_push`'s capacity;
otherwise a generic array is copied to its size and a tag vector keeps its
capacity, `lean_copy_expand_array`). An array's elements
start at offset 24 (every storage type is at most 8 bytes, 8-aligned), so
a read is the handle plus an offset, with no load of a buffer pointer.
Bytes read from a file, standard input or `/dev/urandom` are read into
the array's block (`array::bytes_filled`, lean-runtime's
`Handle::read_uninit` and `RandomSource::fill_uninit`); arrays
built from a Rust `Vec` (`array::from_vec`, `bytes_of_vec`: directory
entries, a process's output, a socket's data) copy its elements once. A release
(of an array, a string, a tag vector or a thunk/task cell)
tests `count == 1` (never `count > 1`): after Reussir's `rc.inc`, which
asserts that the old count was neither 0 nor `u32::MAX`, LLVM then cancels
a read's increment and release. The cost of one block: an array whose
payload is exactly 16 MiB (a hash table's 2^21 buckets) is, with the
header, past mimalloc's large-object limit, a huge segment that mimalloc
purges only 100 ms after it is freed (plan §10, "Arrays and strings are
one block each").
`dbgTraceIfShared` recognizes strings and tag vectors by their Rust type
names (`leanrt::string::`, `leanrt::tagvec::`) besides `reussir_rt::`; it
reports no generic array (sharing is not observable, plan §10).

## Calling convention

The runtime serves the externs of Lean's library (`Init`, `Std`, the
`Lean` package's functions the prelude defines, and lean2rr's shim) under
their C symbols. An `@[extern]` of the program is never bound to it, even
when its symbol is one of these: it runs its own Lean definition, or
lean2rr refuses it, naming Lean's declaration to call instead (translation
plan §5.8, "Externs of the program").

As fixed by lean2rr:

- The extern `lean_xxx` is called as the prelude function `lean_xxx`, with
  the extern's mono-phase parameters in order minus erased ones (types,
  proofs, `lcErased`) and minus the IO world (`lcVoid`).
- Polymorphic externs take explicit storage type arguments:
  `lean_array_push<E>(arr, x)`.
- Functions whose results mention Lean-defined inductive types (`List`,
  `Option`, `Prod`, `Ordering`, `EST.Out`, ...) cannot be written here: the
  prelude offers primitives and generic helpers for lean2rr's glue (below).

Nat positions and indices: a big `Nat` is never a valid position or
index. Where Lean's C code distinguishes "not a scalar" (`>= 2^63`, exactly
the big `Nat`s here) from "out of range", the prelude reproduces that too
(`lean_string_utf8_extract`, where a big position counts as `SIZE_MAX`
since Lean 4.34: a big start gives `""`, a big end extracts to the end;
`Float.scaleB` with Ints outside 32 bits). `String.extract`'s positions are
proved valid: its `lean_string_utf8_extract_fast` (new in Lean 4.34) takes
them with `l2r_index_of_nat`.

## Glue helpers

Generic helpers take the result type's constructors as arguments (nullary
constructors as values, others as curried closures), so lean2rr's glue is a
single call:

| extern | helper |
|---|---|
| `lean_string_compare` (→ `Ordering`) | `l2r_string_compare_with<O>(a, b, lt, eq, gt)`; or `l2r_string_compare(a, b) -> u8` (0/1/2) |
| `lean_string_data` (`String.toList`) | `l2r_string_to_list<L>(s, nil, \|c\| \|t\| cons(c, t))` |
| `lean_string_utf8_get_opt` (→ `Option Char`) | `l2r_string_utf8_get_opt_with<O>(s, p, none, \|c\| some(c))`; or `l2r_string_utf8_get_opt(s, p) -> u32` (`0x110000` = none) |
| `lean_array_to_list` (→ `List α`) | `l2r_array_to_list<E, L>(a, nil, \|x\| \|t\| cons(unbox(x), t))`; `l2r_natarr_to_list<L>`, `l2r_intarr_to_list<L>` |
| `lean_float_frexp`, `lean_float32_frexp` (→ `Float × Int`) | `l2r_float_frexp_with<P>(x, \|m\| \|e\| mk(m, e))`; or `l2r_float_frexp_mant`/`_exp` |
| `lean_io_getenv` (→ `Option String`) | `l2r_io_getenv_with<O>(name, none, \|s\| some(s))` |
| `lean_slice_hash`, `lean_slice_dec_lt` (take `String.Slice`) | `l2r_slice_hash(s, b, e)`, `l2r_slice_dec_lt(s1, b1, e1, s2, b2, e2)` |
| `lean_byteslice_beq` (takes `ByteSlice`s) | `l2r_byteslice_beq(a, startA, stopA, b, startB, stopB)` (fields `byteArray`, `start`, `stop`) |

**IO externs that cannot fail** (BaseIO) have a payload primitive named
`l2r_` + the symbol without `lean_`, taking the same passed arguments;
lean2rr wraps its result with `wrapIOResult`: `l2r_io_mono_ms_now()`,
`l2r_io_mono_nanos_now()`, `l2r_io_process_get_pid()`, `l2r_io_get_num_heartbeats()`,
`l2r_io_check_canceled()`, `l2r_io_get_tid()`, `l2r_io_initializing()`,
`l2r_io_set_heartbeats(n)`, `l2r_runtime_mark_persistent<T>(a)`,
`l2r_runtime_mark_multi_threaded<T>(a)`, `l2r_runtime_forget<T>(a)`,
`l2r_runtime_hold<T>(a)`, `l2r_io_prim_handle_is_eof(h)`,
`l2r_io_prim_handle_is_tty(h)`. (`l2r_io_app_path()`, `l2r_io_current_dir()`
and `l2r_io_process_get_current_dir()` are infallible stand-ins for the
fallible primitives below.) References are Reussir cells in a
lean2rr-generated record (`L2RRefN(Cell<T>)`, two allocations;
translation plan §5.1), read and written by the plain-Reussir helpers
`l2r_rc_get/set/swap<T>` (a `Nat` or `Int` reference holds the handle
like any other). Promises hold the `LCell` of their task
(below). `LRef<T>` and its `l2r_ref_*` functions (a runtime cell, a
0-or-1 element vector) are no longer used by generated code. A `set`
(`l2r_rc_set`, and `l2r_lcell_set` for task and thunk cells) stores the
new value first and then releases the old one as `lean_dec` does
(`leanrt::drop::release`, through `l2r_release_value`): a shared value is
decremented; the last reference to a record is freed inside a free the
runtime starts (`drop::run`), so its fields go last first and the `sync`
dependents of the promises it drops run when that free ends. A unit or
enumeration value cannot cross the FFI boundary and its release runs
nothing: lean2rr stores it with `l2r_rc_put` (`refSetFn`). In a program
that creates tasks (lean2rr's `programCreatesTasks`, translation plan
§5.14 "References") each reference operation first has a point
(`leanrt::refs`): `l2r_ref_read_point()` before `get` (lean-runtime's
`ref_read`, a polling point every 1000 reads), `l2r_ref_write_point()`
before `set` (`before_publish`), `l2r_ref_swap_point()` before `swap`;
each answers whether some reference is taken by a `modify`, and only then
is `l2r_ref_wait(r, store)` called, which waits while another thread holds
reference `r` (or, for the holder's own store, releases it and wakes the
waiters). `take` calls `l2r_ref_take_mark(r)`: it waits the same way, then
records `r` as taken by the running thread (Lean 4.35's rule).

**Freeing containers.** Native Lean frees an object iteratively: the
children whose count drops to zero go on a stack of objects to free, popped
last first. Reussir's drop glue does the same for records with the local
patches 0013 and 0014: the record members it frees go on a stack of
pending work per thread (`reussir_rt::drop`), and it releases a container
field through the container's Rust `Drop` (the opaque type's drop hook),
which releases the elements. The prelude's containers are therefore
`leanrt::drop`'s types, whose `Drop` frees the last reference through
that same stack (so the runtime needs Reussir with 0014): a container
freed while another free runs (from an element's release, or from record
glue) is pushed instead, and the outermost free, glue or container, pops
the stack until it is empty. An array is emptied from its last element,
and what an element's release pushes is done before the next element, so
the order of observable releases matches Lean's (file handles closed, and
so flushed, promises resolved; `fs` and `task` push those too while a free
runs), except at the top of a free that starts at a record that user code
drops by itself (translation plan §10). For an
array of Reussir records (`Bridge` elements), a shared element is
decremented inline instead of through `<record>_ffi_release` (the
compiler's glue, an out-of-line call; it decrements the same count), and,
outside a running free, an array none of whose elements is freed is freed
without the stack (`ReleaseElems`): only an element whose last reference
goes takes the glue and the stack, so the order of releases is unchanged.
(Inside a free the array is pushed as before: a later field of the record
being freed may hold one of its elements.)

**Constants.** A constant's accessor tests its once-cell inline
(`once::claim`'s fast path); the slow path, out of line, computes it or
waits for the scheduler context computing it.

**Thunks and tasks.** A thunk or task is an `LCell<S>` holding a
lean2rr-generated state `enum S { pending(L2RUnit -> α), busy, done(α),
conv(L2RUnit -> α, L2RBox) }` (a task's `conv` also holds the original's
address, its identity for `leanrt::task`, and tasks also have
`bind(L2RUnit -> LCell<S>)`; a shared enum, so any `α` fits). Cell primitives: `l2r_lcell_new<S>(v)`,
`l2r_lcell_get<S>(c)` (a new reference to the state; the cell's own
reference is released first, `drop::cell_get`, so that LLVM cancels it
with the caller's increment), `l2r_lcell_set<S>(c, v)` (a store another
context can see: first lean-runtime's `sched::before_publish`, which waits
for the writers of the streams this context handed off; one relaxed load
when there is none), `l2r_lcell_swap<S>(c, v)` (returns the old state),
`l2r_lcell_addr<S>(c)` (the cell's address).
lean2rr generates the forcing functions (run the closure once, store
`done`); `l2r_lazy_cycle<T>()` waits forever, for a thunk or task needed by
its own computation, as native Lean does.

Tasks run on lean-runtime's scheduler (`lean_runtime::sched`: when a task
runs, its queues, dependents and walks, waits, polling, cancellation,
promises and the final run are its rules; its `docs/sched.md`).
`leanrt::task` is the glue: the cell is the task's slot (its value), and a
cell that is a task lean-runtime has not finished has an entry in a slab
(its `TaskId`, its state type's tag, flags), whose index the cell's 4 bytes
of padding after its count hold (initialized by `l2r_lcell_new`); a task is
named by an address, its cell's or the one a converted task records, and
once its cell holds `done` its id is never given out again
(`TaskId::FINISHED`). A task's job (lean-runtime's `Job`) holds the cell's
address and tag, not a count: run, it gives the generated code a counted
reference (`l2r_task_handed<S>()` / `l2r_task_take<S>()`, with the tag
`l2r_task_next_tag()`) through the program's dispatcher
(`l2r_task_run_one_c`, lean2rr's `l2r_task_run_one`), which runs the task as
a worker would; when lean-runtime drops a job unrun, the glue's reference,
if it holds one, is dropped the same way (`l2r_task_deleting()`). The
program's last reference to an unfinished task is its cell's last: its drop
calls lean-runtime's `release(id)` (Lean's `deactivate_task`, IO tasks
included); a task lean-runtime still runs keeps its cell (the glue holds
that last reference, and the job gets it). The generated code's primitives
(unchanged from leanrt's own scheduler, so the program's code is the same):
`l2r_task_register<S>(c, tag, prio, kind)` (a new task: lean-runtime's
`spawn`, which may run it at once, at priority 2^32-1; `prio` as Lean passes
it; `kind` 1 pure (`keep_alive` false), 2 a dependent: recorded until
`l2r_task_depend_at(src, dep, sync)`, which is `depend`), `l2r_task_begin<S>(c)`
(1 when the task runs as on a worker thread, with stream cells of its own:
lean-runtime's `Glue::task_begin`), `l2r_task_end<S>(c)` (its cell holds its
value: finished for lean2rr; 0: lean-runtime walks its dependents),
`l2r_task_bind_wait<S>(c, src)` (a `bind` task whose function returned the
unfinished task `src`: its job returns `Outcome::Continue`),
`l2r_task_source_next_at(a)` and `l2r_task_wait_running(a)` (lean-runtime's
`wait`, after the Lean panic of `Task.get` in a `sync := true` task; none
for the task a job is about to run), `l2r_task_status_at(a)` (2 finished, 1
not), `l2r_task_query_at(a)` (`IO.getTaskState`: lean-runtime's `state`),
`l2r_task_wait_status_at(a)` and `l2r_task_wait_progress()` (`IO.waitAny`:
the generated loop's two passes collect the list, then lean-runtime's
`wait_any` chooses, and the next pass takes the task at its position),
`l2r_task_cancel_at(a)`, `l2r_task_check_canceled()`,
`l2r_task_deferring()` (lean-runtime's `deferring`: false during
initialization and with `LEAN_NUM_THREADS=0`, when Lean runs tasks at once;
set from the numbers `main`'s start read), `l2r_task_manager_start()`
(before `main`: the task manager's number of workers and stack size, read
as natively; lean-runtime's scheduler starts with them, with leanrt's
glue, at the first task, promise, `Std.Sync` object, timer, signal watcher
or socket: lean-runtime's lazy start, `sched::start_lazy`, whose entry
points call `ensure_started`) and `l2r_task_shutdown()` (after `main`:
lean-runtime's `finish`, the final run, then the io layer's dedicated
tasks; without a built scheduler, the same without the run). The generated walks
(`l2r_task_walk_next()`, `l2r_task_walk_if`) and the generated final run
(`l2r_run_pending_tasks`) find nothing: lean-runtime does them.
`l2r_sleep_ms` is lean-runtime's `sleep_ms`. Standard streams are per task,
as they are per thread natively: `l2r_std_push(base)` / `l2r_std_pop(base)`
set the stream cells aside and put them back
(`leanrt::once::push_context`), and `l2r_once_take<T>(slot)` empties a
cell.

**The scheduler** (lean-runtime's `sched`, features `sched` and
`stack-overflow`; `leanrt::sched` is the glue; translation plan §5.14,
*Blocking*). Code that blocks (a contended lock, a condition variable, a
task running on another context or a promise not resolved yet, a sleep, a
read of an empty pipe, the final run after `main`) suspends its *context*
(`main`'s thread stack, or a corosensei stack of a worker thread's size, 1
GiB, with a guard page) and lean-runtime's hub runs the contexts that can
go on, queued tasks on new contexts within Lean's number of workers
(`LEAN_NUM_THREADS`, or the online processors), or waits in its event loop.
The glue: `Glue::suspend` (the one `unsafe` step, its `SAFETY` entry in
`leanrt::sched`), `Glue::switched` (each context's current standard streams
and saved stream contexts, `once::CtxState`, set aside and given back at
each switch), `Glue::task_begin`/`task_end` (whether a task runs as on a
worker thread of its own, which `l2r_task_begin` answers), the waits of a
`busy` thunk and of a constant another context computes (lean-runtime's
wait cores, core 3.1: `l2r_thunk_wait_busy(a)` is `wait_running_keyed(a)`,
`l2r_thunk_done(a)` is `done_keyed(a)`, under the thunk's address;
`once::claim`'s cold path is `step_keyed`, a constant's store
`done_keyed`, under the odd key `(slot << 1) | 1`), the references of a
program that creates tasks (core 3.2, `leanrt::refs`), and the no-suspend
scope: a stream handle's drop runs in `sched::no_suspend()`, where a
dropped stream's flush hands what would wait to a writer thread, so no
context is suspended inside a free (the free is the thread's,
`reussir_rt::drop`). A promise dropped inside a free is resolved with
`none`, its cell's store included, only once the free is over (core 3.3:
when the free reaches it, in Lean's order, `task::defer_promise_drop` puts
the resolution off with `defer`; the drain's end runs the resolutions in
that order, on this context, with `run_deferred`), since its dependents
are Lean code that may block. Reussir reports every drain's end through
`__reussir_drop_drained`, its local patch 0040, which lean2rr requires:
`scripts/l2r.py` stops with an error when the Reussir checkout lacks it,
and leanrt names the symbol (`task::hook_drained`), so it would not link
without it. Output
(`io::stream_put`, `fs::put_str`, `fs::flush`, a panic's lines), spawning a
process and `IO.Process.exit` are lean-runtime's effect points
(`sched::effect`); the program's clock reads are polling points
(`io::mono_nanos_polled`, `realtime_nanos_polled`). Lean's stack-overflow
report is lean-runtime's (`rt::install_stack_overflow_handler` on each
thread that runs Lean code). `LEAN_NUM_THREADS=0` (C's `atoi`) is no task
manager: tasks run at once.

**`Std.Sync`** (`leanrt::sync`, over lean-runtime's `sched::sync`):
`BaseMutex`, `Condvar`, `BaseRecursiveMutex`, `BaseSharedMutex` are
`LHandle`s holding lean-runtime's objects; the externs' payloads are
`l2r_io_basemutex_new()`, `l2r_io_basemutex_lock(m)`, ... (over
`l2r_sync_new(kind)`, `l2r_sync_op(op, h)`, `l2r_condvar_wait_h(c, m)`).
The rules are lean-runtime's: a lock is owned by a thread (the context and
its innermost running task's thread); waiting blocks the context; an
unlock hands the lock to the longest waiter; relocking a held `BaseMutex`
waits forever (glibc); the shared mutex is libc++'s.

**The event loop** (lean-runtime's: `sched::uv` for `Std.Internal.UV`'s
loop, timers and signal watchers, `net` for its TCP and UDP sockets, name
resolution and interface addresses; `leanrt::net` converts, for
`lean2rr/L2RShim.lean`): timers, signal watchers and sockets are `LHandle`s
over lean-runtime's objects; an operation returns an `Op` handle (`OpSt`:
done, canceled, a value code, the start's and the completion's errors
(lean-runtime's `IoError`s, read as the `IO.Error` builder, code, file name
and details: `l2r_shim_op_err_*`), bytes, an address, strings, a new
socket, and, for `next`, whether the loop took the promise passed or the
one it had) read by `l2r_shim_op_*`. An operation completing later takes a
promise `r` from the shim; lean-runtime's completion closure
(`net::Completion`) stores the outcome and drops its reference to `r` on
lean-runtime's loop context, which runs the shim's continuation (a `sync`
dependent of `r`); a closure lean-runtime drops uncalled (`cancelRecv`,
`cancelAccept`, a timer stopped or canceled) marks the operation canceled.
A timer's or watcher's loop promise is `net::LoopP` (lean-runtime's
`LoopPromise`: the program's promise and the completion that resolves it).
The primitives (`l2r_shim_*`, the payloads of the shim's `lean_shim_*`
externs): the loop (`loop_configure`; `l2r_uv_event_loop_alive`), timers
and signals (`timer_new`, `timer_next`, `timer_ctl`, `signal_new`,
`signal_next`, `signal_ctl`), TCP (`tcp_new`, `tcp_bind`, `tcp_listen`,
`tcp_connect`, `tcp_send`, `tcp_recv`, `tcp_wait_readable`,
`tcp_cancel_recv`, `tcp_accept`, `tcp_try_accept`, `tcp_cancel_accept`,
`tcp_shutdown`, `tcp_name`, `tcp_nodelay`, `tcp_keepalive`), UDP (`udp_new`,
`udp_bind`, `udp_connect`, `udp_send`, `udp_recv`, `udp_wait_readable`,
`udp_cancel_recv`, `udp_name`, `udp_option`, `udp_membership`,
`udp_multicast_interface`), name resolution (`dns_get_info`,
`dns_get_name`), interfaces (`ifaces`), the pure `lean_shim_pton`,
`lean_shim_ntop` (lean-runtime's `semantics::net`); `Std.Internal.UV.System`
over `leanrt::sys`, the glue of lean-runtime's `io::uvsys` (`sys_title_set`,
`sys_query(which)` for the queries with a string or several results, the
process title included, `sys_group`, `sys_getenv`, `sys_priority`,
`sys_word(which)` for single numbers, `sys_chdir`, `sys_setenv`,
`sys_setpriority`, `sys_random`, completed on lean-runtime's loop context,
`net::complete_on_loop`): lean-runtime's ports of libuv's Linux code with
the buffers Lean passes; `setProcessTitle` writes the title into the
arguments' memory, so `/proc/self/cmdline` shows it, as natively (feature
`proc-title`); and `windows_next_transition`,
`windows_local_timezone_id_at` (`Std.Time.Database.Windows`, which fails
off Windows: lean-runtime's `io::time` errors). A system query's error is
lean-runtime's (`decode_uv_error(code, name)` with `chdir`'s path and
`osGetGroup`'s `"group"`, `embedded_nul` for a string holding a NUL byte),
kept as the operation's start error, which the shim throws (`checkStart`,
as for the sockets); a query's `none` (no such group, an unset variable) is
code 1. `TCP.Socket.new` and `UDP.Socket.new` give an operation holding
the socket, or lean-runtime's error, an `IO.Error` as natively (libuv 1.48
never fails there). An
operation's strings are decoded as `lean_mk_string` does (invalid UTF-8
becomes U+FFFD). Addresses are byte arrays: the family (4 or 6), the port
(big-endian, for socket addresses), the address bytes. The shim's
`l2r_shim_promise_is_resolved(p)` answers `IO.Promise.isResolved`
(`task::promise_is_resolved`, as `IO.getTaskState` answers for the
promise's task) and then releases `p`: natively `isResolved` borrows the
promise, so a last reference resolves it with `none` only after the
question.

**Promises.** `LPromise` is a runtime object holding the cell of the
promise's task (`leanrt::task::Promise`); lean-runtime's promise id is that
task's: `l2r_promise_new<S>(c)` (lean-runtime's `promise_new`: Lean's
internal panic before `main`), `l2r_promise_cell<S>(p)` (the task, a new
reference), `l2r_promise_release(p)`, and `l2r_task_resolve_at(a)` after
the generated code has stored the value (lean-runtime's `resolve`, which
walks the dependents; inside a free, once it is over). When the last
reference to a promise goes, the runtime calls the program's
`l2r_promise_drop_c(cell)` (a trampoline lean2rr exports), which resolves an
unresolved promise with `none`. `l2r_option_get_or_block_none<T>()` is
`Option.getOrBlock!` on `none` (`Promise.result!` of a dropped promise):
lean-runtime's `option_get_or_block`, with Lean's forced panic message
(`leanrt::lean_panic`), then the running context blocks forever, as
natively the calling thread does: the other tasks and `main` go on.

**Fallible IO** (files, standard streams, processes): primitives record
their outcome in a global last-error slot (`leanrt::fs`: nothing, or
lean-runtime's `IoError`); the glue is

    let v = l2r_fs_open(path, modeIndex);
    l2r_io_finish(v, |v| EST.Out.ok(v), |kind| |errno| |fname| |details| mkError)

where `mkError` builds the `IO.Error` with the `lean_mk_io_error_*`
constructor (exported Lean functions) numbered `kind` (`fs::kind_of`: the
`IoError`'s constructor, and for those with an optional file name whether
it has one):

| kind | constructor (`lean_mk_io_error_…`) | kind | constructor |
|---|---|---|---|
| 0 | `other_error(errno, details)` | 12 | `no_such_thing_file(fname, errno, details)` |
| 1 | `interrupted(fname, errno, details)` | 13 | `already_exists(errno, details)` |
| 2 | `invalid_argument(errno, details)` | 14 | `already_exists_file(fname, errno, details)` |
| 3 | `invalid_argument_file(fname, errno, details)` | 15 | `hardware_fault(errno, details)` |
| 4 | `no_file_or_directory(fname, errno, details)` | 16 | `unsatisfied_constraints(errno, details)` |
| 5 | `permission_denied(errno, details)` | 17 | `illegal_operation(errno, details)` |
| 6 | `permission_denied_file(fname, errno, details)` | 18 | `resource_vanished(errno, details)` |
| 7 | `resource_exhausted(errno, details)` | 19 | `protocol_error(errno, details)` |
| 8 | `resource_exhausted_file(fname, errno, details)` | 20 | `time_expired(errno, details)` |
| 9 | `inappropriate_type(errno, details)` | 21 | `resource_busy(errno, details)` |
| 10 | `inappropriate_type_file(fname, errno, details)` | 22 | `unsupported_operation(errno, details)` |
| 11 | `no_such_thing(errno, details)` | 23 | `IO.userError(details)` |

The decoding is lean-runtime's (`io::error`): since Lean 4.34 the kind and
the details come from libuv's code for the errno (`decode_uv_error_impl`
in io.cpp; `crt_to_uv` maps the errnos libuv cannot represent to the
closest code it can, e.g. `EBADMSG` to `EPROTO`, a protocol error): the
details are `uv_strerror`'s ("illegal operation on a directory" for
`EISDIR`, "Unknown system error -122" for an errno libuv has no name for),
not `strerror`'s; the error code stays the errno. The operations Lean
implements with libuv (`removeFile`, `hardLink`, `metadata`,
`symlinkMetadata`, `createTempFile`, `createTempDir`) report errors as
`decode_uv_error`: classified by libuv's code (errnos it has no case for
are kind 0), `uv_strerror`'s details, and the positive errno as the error
code (`2` for `ENOENT`). `leanrt`'s unit test `fs_tests.rs` checks both
decoders, through the slot, against native Lean for every errno 0..140
(test `RtIOErrorDecode` checks reachable cases end to end). Kind 23 is
Lean's `io_result_mk_error(msg)` (`IO.currentDir`, `IO.appPath`, a child's
output that is not UTF-8).

File primitives: `l2r_fs_open(path, mode)` (mode = `IO.FS.Mode` constructor
index), `l2r_fs_put_str`, `l2r_fs_write`, `l2r_fs_flush`, `l2r_fs_read(h, n)`,
`l2r_fs_get_line`, `l2r_fs_rewind`, `l2r_fs_truncate`,
`l2r_fs_lock(h, exclusive)`, `l2r_fs_try_lock`, `l2r_fs_unlock`,
`l2r_fs_remove_file`, `l2r_fs_create_dir`, `l2r_fs_remove_dir`,
`l2r_fs_rename`, `l2r_fs_hard_link`, `l2r_fs_set_access_rights` (for
`lean_chmod`), `l2r_fs_real_path`, `l2r_fs_read_dir(p) -> RVec<LStr>` (names
in `readdir` order), `l2r_fs_metadata(p, follow) -> RVec<u64>` ([atime s,
ns, mtime s, ns, size, `FileType` index, numLinks]; the seconds are `i64`
bit patterns), `l2r_fs_current_dir()`, `l2r_fs_app_path()`,
`l2r_fs_process_get_current_dir()`, `l2r_fs_process_set_current_dir(p)`,
`l2r_fs_create_tempfile() -> LHandle` (then `l2r_fs_temp_file_path()` is
its path, for the `Handle × FilePath` pair), `l2r_fs_create_tempdir()`,
`l2r_fs_get_random_bytes(n)` (`IO.getRandomBytes`, from `/dev/urandom`).
Each is a `leanrt::fs` function over lean-runtime's (`Handle`, `io::fs`,
`io::temp`, `io::env`).

**Sinks.** lean-runtime appends its results of unbounded size (a line, a
path, a child's output) to a `ByteSink` the glue gives it; `getLine`
appends while it holds the stream's lock. A line, a path, a name or an
environment value goes into a plain `Vec<u8>`, infallible as
lean-runtime's contract asks: a failed allocation aborts (Rust's `memory
allocation of N bytes failed`, status 134; native's `std::bad_alloc` aborts
with 134 too), so the process never exits under the lock (its exit would
wait for it) and `getLine` of a line without end ends (test
`RtLineNoEnd`). A child's output (`IO.Process.output`) goes into
lean-runtime's `StoppingSink`, which grows with `try_reserve` and, when
that fails, drops the bytes and says it has stopped (`ByteSink::stopped`;
lean-runtime then stops reading); once lean-runtime has returned, a
stopped sink ends the process with `INTERNAL PANIC: out of memory`
(`proc::output`), as Lean's failed allocation of the growing `ByteArray`
does (AR-5).

**stdio model.** Handles and the standard streams are lean-runtime's
models of glibc's `FILE` (`io::cfile`, following libio's
`fileops.c`/`genops.c` function by function; leanrt's own model moved
there): one `st_blksize` buffer shared by reading and writing with libio's
get/put areas and cached offset; `fwrite` (`_IO_new_file_xsputn`,
line-buffered tails flushed at each newline), `fread` (`_IO_file_xsgetn`,
including direct reads of whole blocks), `getc`, `fflush`, `fseek`
(in-buffer seeks), `ftello`; `EBADF` for the wrong direction after the
same mode switch; sticky end-of-file and error indicators (after any
failed operation on a handle, `getLine` fails, as natively); reading a
terminal first flushes a line-buffered stdout. The same system calls
happen in the same order, so the `errno`s are native's (lean-runtime keeps
its own model of `errno`, `io::error::errno`). At exit (`io::exit`),
stdout is flushed first (libc++'s `ios_base::Init`), then every `FILE`'s
pending output, newest first, then used streams are synced (a seekable
stdin is left at the position the program read up to).

Standard-stream primitives (`fd` = 0 stdin, 1 stdout, 2 stderr; the fields
of `IO.FS.Stream`): `l2r_stream_putStr(fd, s)`, `l2r_stream_write(fd, b)`,
`l2r_stream_flush(fd)`, `l2r_stream_read(fd, n)` and
`l2r_stream_getLine(fd)` record their outcome like the file primitives
(`EPIPE`, `EBADF` for the wrong direction, `EINVAL` on streams that were
closed at startup); `l2r_stream_isTty(fd)` cannot fail.

**Child processes** (lean-runtime's `io::process`: `IO.Process.spawn` over
`posix_spawn`, with what Lean's forked child does before `execvp`
reproduced, pipes with `O_CLOEXEC`, stdout flushed first when the child
inherits stdin; a `null` stream's `/dev/null` is opened by the parent with
`O_CLOEXEC`, see "Known divergences from native Lean"):
`l2r_proc_spawn(cmd, args, cwd, has_cwd, env_names, env_values, env_set,
modes, inherit_env, setsid) -> u32` (the pid; fallible; `modes` = stdin |
stdout << 8 | stderr << 16 as `IO.Process.Stdio` indices; `env` as parallel
arrays, `env_set[i]` for `some`), then `l2r_proc_end(0/1/2) -> LHandle` (the
parent's end of a piped stream, a handle that is not open otherwise);
`l2r_proc_wait(pid) -> u32` (128 + signal when killed),
`l2r_proc_try_wait(pid) -> u64` (`1 << 32 | code` once exited, 0 while
running), `l2r_proc_kill(pid, setsid)` — all fallible; `leanrt::proc` keeps
each child's process object by pid for them until the child is reaped, and
then makes the system call on the pid itself, as natively (`ECHILD`,
`ESRCH`). A child that cannot change
directory or execute prints Lean's message and exits with 255, its stdout
first getting the bytes the parent had pending, as natively (lean-runtime
starts a stand-in process for it). `IO.Process.output` reads stdout in a
dedicated task while it reads stderr; lean2rr's tasks are deferred, so
lean2rr replaces its body with `l2r_proc_output(cmd, args, cwd, has_cwd,
env_names, env_values, env_set, inherit_env, setsid, input, has_input) ->
u32` (lean-runtime's `io::process::output`: both pipes read to end of file
together with `poll`; `readToEnd`'s UTF-8 checks and the errors in Lean's
order; fallible) and `l2r_proc_output_str(1/2) -> LStr` (stdout, stderr).

**Other glue primitives.**

| Lean | primitives |
|---|---|
| `initialize`, closed terms | once-cells `l2r_once_claim(slot)` (`l2r_once_has` for the mutable cells), `l2r_once_get<T>(slot)`, `l2r_once_set<T>(slot, v)` |
| `IO.setStdout`/`setStderr`/`setStdin` | a cell per stream: `l2r_once_*` plus `l2r_cell_swap<T>(slot, v) -> T` (returns the previous value) |
| `timeit`, `allocprof` | `l2r_io_timeit_with<R>(msg, act)`, `l2r_io_allocprof_with<R>(msg, act)` (their lines are lean-runtime's: `io::time::timeit_line`, `io::debug::ALLOCPROF_NOTE`) |
| `Void.mk` | `lean_void_mk<T>(x)` |

**Main thread.** `leanrt::rt::run_main2(|| init(), || body())` runs
`init` (the module initializers) on the calling thread, as native `main`
does, then `body` as `lean_run_main` does: lean-runtime's
`io::startup::run_main` (audit item 4.2), on a thread with a 1 GiB stack
(`sched::thread_stack_size`, `LEAN_STACK_SIZE_KB`), or on the calling
thread with `LEAN_MAIN_USE_THREAD=0`. The thread has no name of its own:
it keeps the process's (`/proc/thread-self/comm`), as native's `lthread`
(until switch step 7 lean2rr named it `main`; a Rust panic's header there
now says `thread '<unnamed>'`). A Rust panic (a runtime bug) inside the
generated code (`l2r_main_body` and every frame below it, the runtime's
textures included) cannot unwind: Rust reports "panic in a function that
cannot unwind" and aborts, status 134, buffered stdout lost, in both
modes, as before step 7. Only a panic in the glue's own frames
(`run_main2`'s closure, `install_stack_overflow_handler`) comes back from
`run_main` as `Err`, and the process exits with status 101, its streams
written. Both threads have Lean's stack-overflow report
(lean-runtime's, feature `stack-overflow`: a fault in the guard page of
the thread's stack, or of the scheduler's context running on it, prints
`\nStack overflow detected. Aborting.` and aborts, exit 134, without
flushing stdout — as native): `install_stack_overflow_handler` at the
thread's entry (for `main`'s thread, first in the body `run_main2` gives
`run_main`; the scheduler's start registers it again). `body` holds the
whole of `main`'s life with tasks (`task::start`, `main`,
`task::shutdown`): the scheduler's state is the thread's own. `main`'s
thread allocates on transparent huge pages, as native Lean's mimalloc
does: no constructor allocates before mimalloc's own (lean-runtime's
AR-36), so the process's main thread reserves the first arena with large
OS pages (until switch step 7 leanrt set mimalloc v2's
`eager_commit_delay` to 0 for it, `alloc::heap_on_huge_pages`; implementation
notes, startup/entry.md). Before `main`, lean-runtime's own
ELF constructor (feature `startup-fds`, `.init_array.00101`, audit item
4.3) opens the descriptors native Lean's runtime has open at startup
(`io::startup`: libuv's epoll descriptor, two io_uring rings when the
kernel has them, real rings mapped as libuv maps them, the signal lock
pipe with its byte, the loop's signal pipe and an eventfd, close-on-exec,
in that order at the lowest free numbers): `/proc/self/fd`, descriptor
numbers and `EMFILE` thresholds are native's, and a standard descriptor
closed at startup is taken by the first of them, as natively (using it
fails with `EINVAL`, children see it closed). When they cannot be made,
the program ends before `main` with `INTERNAL PANIC: Failed to initialize
event loop: ...` and status 1 (natively a crash or an abort: LB-30,
LB-31). Running before Rust's runtime, the constructor also keeps Rust
from putting `/dev/null` in the place of closed standard descriptors.
`run_main2` calls `io::startup::ensure_native_descriptors()` first, which
keeps the constructor linked and, if it did not act (it acts only in the
program's own executable: under `ld.so ./prog` or without `/proc` it does
nothing, lean-runtime's accepted deviations RSH2-11), opens them where
they land; it closes nothing (until switch step 7 lean2rr's own
constructor and fallback, which closed Rust's read-write `/dev/null`s on
descriptors 0 to 2 first, did this: lean-runtime's reviews RSH2-04 and
LS2-01 dropped that recovery).
Signal watchers use the loop's signal pipe, as libuv's loop does
(lean-runtime's `sched::uv` claims it from `io::startup`).
`IO.initializing` is lean-runtime's flag (`io::startup`), true until the
entry's `l2r_set_initializing(false)` after the module initializers
(`mark_end_initialization`). `main`'s return (`l2r_exit`) and an uncaught
error first wait for lean-runtime's dedicated tasks (`io::exit::after_main`:
the stdout readers `IO.Process.output` leaves running when stderr fails),
as `lean_finalize_task_manager` does; `IO.Process.exit` and panics do not.
`IO.Process.forceExit` is `_exit` (lean-runtime's `force_exit` is
`std::process::exit`, which runs the handlers of linked C code; its
documentation asks a glue that needs `_Exit` to call `_exit`), once the
writers of the streams the context handed off have ended
(`io::force_exit`).

## Requests for lean2rr

Found while testing the runtime; items marked *done* are handled by
lean2rr's dev branch (the tests pass with it).

1. *done* — Constructors with extern implementations (`Int.ofNat`,
   `Int.negSucc`) are extern calls, not constructors of `Int`.
2. *done* — Propositions (`ByteArray.IsValidUTF8`) have no representation,
   and proofs are not passed to externs.
3. *done* — Extern type arguments are mono types (one-field structures
   unwrapped).
4. *done* — Only type-variable positions of polymorphic externs are boxed
   (`Array.get!Internal @[Nat]` used to box the index).
5. *done* — Glue for `String.compare`, `String.toList`, `String.get?`,
   `Float.frExp`, `String.intercalate`, `Array.toList`, `ST.Ref`.
6. *done* — Element-wise `RVec` conversion between instantiations
   (`RtHashMap`), and the `unsafeCast`-based `Array.mapMUnsafe`/
   `Array.modifyM` implementations (`RtArrayUnsafe`).
7. *done* — `BaseIO.asTask` (symbol `lean_io_as_task`): the task glue is
   keyed on `IO.asTask`, which is not the extern (Lean 4.33, 4.34).
8. *done* — `dbgTrace` (and `dbgSleep`, `dbgStackTrace`, `Thunk.mk`) at a
   boxed `α`: the `PUnit → α` closure argument must be wrapped to return the
   box (`lean_dbg_trace<ElemBox>(msg, f : L2RUnit -> Nat)` does not
   type-check). lean2rr now instantiates generic prelude functions that are
   plain Reussir code at the value type (`lean_dbg_trace<Nat>`), and thunks
   and tasks are cells of a generated state type.
9. *done* — BaseIO payload primitives above (`IO.monoMsNow`, `IO.getRandomBytes`,
   ...) and the file protocol need `wrapIOResult` glue; `IO.FS.Handle`
   (`lcAny` in mono code) must be represented as `LHandle`.
10. *done* — Externs implemented by `@[export sym]` Lean code (all
    `Substring.Raw.Internal.*`, many `String.Internal.*`,
    `lean_array_to_list_impl`, `IO.eprint(ln)`, `lean_stream_of_handle`, the
    `IO.Error` constructors, `Lean.Name.beq` has a reference body) should
    compile and call that code (`Mono.redirectTarget`). The prelude's
    hand-written versions of the `String.Internal.*` ones, never called
    since, are deleted.
11. *done* — `Array Nat`/`Array Int` as `LNatArr`/`LIntArr` (names above).
12. *done* — `Nat.repr`/`Int.repr` of big numbers are Lean code dividing by 10 digit
    by digit (quadratic); `l2r_nat_repr`/`l2r_int_repr` are exact
    replacements using GMP.
13. *done* — The generated entry should run `l2r_main_body` through
    `leanrt::rt::run_main(|| unsafe { l2r_main_body() })` instead of its
    own `std::thread` (Lean's stack size incl. `LEAN_STACK_SIZE_KB` and
    `LEAN_MAIN_USE_THREAD`, and Lean's stack-overflow message; test
    `RtStack`). (Since item 24 the entry calls `run_main2`; since switch
    step 7 its thread is lean-runtime's `io::startup::run_main`, and
    `run_main` is gone.)
14. *done* — The standard-stream glue should check each `l2r_stream_*` call with
    `l2r_io_finish`, as for files (tests `RtBrokenPipe`, `RtClosedStreams`).
15. *done* — `lean_io_prim_handle_is_tty` and `lean_io_prim_handle_is_eof` are
    `BaseIO`: the `lean_io_prim_handle_` prefix rule sends them to the
    fallible glue, which rejects them ("IO result ... cannot fail"). Use the
    BaseIO payloads `l2r_io_prim_handle_is_tty`/`_is_eof` (test
    `RtHandleIsTty`).
16. *done* — `ST.Prim.Ref.take` is lowered to `l2r_ref_get`, so the value stays in
    the cell and the taken copy is shared: every `modify`/`modifyGet`
    copies the array or string it updates (quadratic loops). Map it to
    `l2r_ref_take` (now `l2r_rc_swap` with the placeholder).
17. *done* — `allocprof` (`lean_io_allocprof`) has no glue: use
    `l2r_io_allocprof_with(msg, act)` (test `RtAllocProf`); likewise
    `timeit` → `l2r_io_timeit_with`.
18. *done* — `lean_chmod` (`IO.setAccessRights`) is not a fallible IO symbol yet; its
    primitive is `l2r_fs_set_access_rights(p, mode)`.
19. *done* — Glue for `IO.FS.createTempFile` (`l2r_fs_create_tempfile` then
    `l2r_fs_temp_file_path` for the pair) and `IO.FS.createTempDir`
    (`l2r_fs_create_tempdir`).
20. *done* — `IO.currentDir`, `IO.appPath` can fail with a user error (kind 23), and
    `IO.Process.getCurrentDir`/`setCurrentDir` with errno errors: use
    `l2r_fs_current_dir`, `l2r_fs_app_path`,
    `l2r_fs_process_get_current_dir`, `l2r_fs_process_set_current_dir`
    with `l2r_io_finish`; kind 23 needs `IO.userError`.
21. *done* on the runtime side — native `panic!` (outside
    `LEAN_ABORT_ON_PANIC`), the runtime's own panics (`index out of
    bounds`, `String.get!`), `dbgTrace`, `dbgTraceIfShared`, `timeit` and
    `allocprof` print to the *current* stderr stream (`io_eprintln`):
    every program defines `fn l2r_stderr_put(s : LStr) -> u64` (lean2rr),
    which the prelude calls. Internal panics, uncaught exceptions and
    abort-mode panics go to descriptor 2, as natively. The runtime's own
    panics are raised inside the prelude's array helpers, which the stream
    code behind `l2r_stderr_put` uses too; a Reussir-level call there
    makes rrc crash in `TokenReusePass` under `--reuse-across-call` (a
    Reussir bug), so they (and `dbgTraceIfShared`, an FFI import) reach it
    from Rust (`leanrt::io::diag_put`) through the trampoline
    `extern "C" trampoline "l2r_stderr_put_c" = l2r_stderr_put;`, which
    lean2rr must emit in every program (a weak symbol: without it they go
    to descriptor 2; test `RtStreamsRedirectOob`).
22. *done* — `String.mk`/`List.asString` (`lean_string_mk`) take a `List Char`: glue
    folding the list with `lean_string_push` onto `lean_mk_string("")`.
23. *done* — `IO.initializing` is true while module initializers run (native
    `g_initializing` until `lean_io_mark_end_initialization`): the entry
    should call `l2r_set_initializing(true)` before the initializers and
    `l2r_set_initializing(false)` after (test `RtInitializing`).
24. *done* — Native `main` runs the module initializers on the process's main thread
    (8 MiB stack) and only `main` on Lean's big thread: the entry should be
    `leanrt::rt::run_main2(|| init(), || body())`, which runs `init` on the
    calling thread (with the stack-overflow report) and then `body` as
    `run_main` (test `RtInitStack`: a deep initializer overflows natively).
    An initializer's uncaught error prints `uncaught exception: ...` and
    exits 1 without running `main`, as natively.
25. *done* — `IO.getEnv` (`lean_io_getenv`) is emitted as a direct call to
    `lean_io_getenv`, which the prelude cannot define (its result is
    `Option String`); use `l2r_io_getenv_with(name, none, some)`.
26. *done* — `IO.Process.forceExit` (`lean_io_force_exit`, `std::_Exit`: nothing is
    flushed) has no glue: as `IO.Process.exit`, with
    `l2r_process_force_exit(code)` (test `RtForceExit`).
27. *done* — `Nat.repr`/`Int.repr` (request 12): besides the quadratic big case,
    `Nat.reprFast` clones the `Nat.reprArray` once-cell and drops it out of
    line for every number ≥ 128 (13% of the Sieve benchmark).
28. *done* — `ByteSlice.beq` needs glue (`l2r_byteslice_beq` above);
    `ShareCommon.State.shareCommon` (`lean_state_sharecommon`, hash-consing
    natively) can use its reference body `(a, s)`, which is observably the
    same (sharing is not observable here).
29. *done* — Child processes: `IO.Process.spawn` and `Child.wait`/`tryWait`/`kill`/
    `pid`/`takeStdin` need glue over the `l2r_proc_*` primitives (above).
    Natively a `Child` object also carries the pid (`uint32`) and whether it
    was spawned with `setsid` (`uint8`) after its three Lean fields, so
    lean2rr's `Child` record needs those two extra fields, set by the spawn
    glue and kept by `takeStdin` (test `RtProcess`). `IO.Process.output`
    should use a runtime primitive (now `l2r_proc_output`, above) instead
    of its task-based reads.
30. *done* — `Lean.Name.beq` (`lean_name_eq`): the prelude cannot define it (`Name`
    is a Lean type); its reference body (structural equality) is what the
    native code computes.
31. *done* — `ptrAddrUnsafe` of a value lean2rr wrapped at the call
    (`ElemBox{x}`, function-value wrappers) measured the temporary wrapper,
    whose memory the next wrapper can reuse. lean2rr now takes the value in
    its own representation (not converted for the call): a heap value's
    handle goes to `l2r_ptr_addr_obj`/`l2r_ptr_addr_rec`, which answer the
    pointer whatever the count (`ptrEq a b` may release `a`'s last other
    reference before `b`'s address is taken), and a `[value]` struct
    answers its field's (translation plan §9; tests `RtPtrAddr`,
    `RtPtrSound`).
32. The `Lean` package's C++ externs (`Expr`/`Level` internals, the
    kernel, `evalConst`, `Dynlib`, `.olean` files, configuration queries):
    not in the runtime. They are Lean's library, so lean2rr does not run
    their Lean bodies in their place (translation plan §5.8): it rejects a
    program that reaches one, naming each (test `RtLeanUnsupported`,
    expected to fail).

For Reussir: `[value]` records across the FFI boundary would let arrays
store enum-like values directly; and `mi_free` takes mimalloc's
generic path (`mi_free_generic_local`, `_mi_page_ptr_unalign`) for most
frees in allocation-heavy loops (30% of an array-update benchmark).

## Known divergences from native Lean

- lean-runtime does not reproduce the Lean runtime bugs of its IO
  (lean-runtime's docs/lean-bugs.md; plan §10, "Runtime: Lean bugs we do not
  reproduce"), so neither does lean2rr:
  - a read of at least one buffer right after output on the same handle
    writes the pending output first and then reads from the cursor
    (`io::cfile`'s `xsgetn`; where the output cannot be written because
    seeking back over read-ahead fails, on a FIFO, it is dropped as
    natively); natively glibc drops the pending bytes (LB-02);
  - a child's `null` stream is `/dev/null` opened by the parent,
    close-on-exec, so the program inherits no extra descriptor, and a
    failed open (`EMFILE`) is the spawn's error (the descriptors made so far
    are closed). Natively the forked child opens it, keeps the descriptor
    open across `execvp` (LB-15), and ignores a failed open, so the program
    then runs on the parent's own stream (LB-17). So a spawn in which some
    `null` stream follows a piped one needs exactly one more free
    descriptor than natively (one in all, however many such streams), where
    the child has closed the pipe's other end before its open; any other
    spawn needs as many. Tests `RtProcessNullFd`, `RtProcessNullOpenFails`;
  - the `Child` that `takeStdin` returns keeps the `setsid` flag, so `kill`
    still signals the group (natively the flag is lost: LB-14);
  - a temporary directory of 4083 to 4095 bytes is tried (natively an
    assertion aborts: LB-16), and a nameless `ENOENT` or `EINTR` error gets
    the file name `""` (below; LB-03);
  - startup descriptors that cannot be made end the program with lean-runtime's
    `INTERNAL PANIC` (natively a crash or an abort: LB-30, LB-31; test
    `RtStartupFdExhausted`); an exit does not wait for a stream whose holder
    is blocked reading it (LB-29).
- Panics print `backtrace:` and `(stack trace unavailable)` instead of a
  stack trace (unless `LEAN_BACKTRACE=0`, which prints neither, as native).
- Sharing is not observable: `isExclusiveUnsafe` answers `false`, and
  `dbgTraceIfShared` of values held by value (`[value]` structures, small
  `Nat`s) never reports sharing. Pointer identity is not emulated (translation
  plan §9): `ptrAddrUnsafe` answers the handle pointer of a heap value in
  its own representation (`l2r_ptr_addr_obj`, `l2r_ptr_addr_rec`, which
  give the reference back inline), the boxed scalar `2n+1` for
  `UInt8/16/32`, `Char`, `Bool`, enumerations and `Unit` (`l2r_addr_word`),
  a `Nat` or `Int` its own word, which is native Lean's (`l2r_addr_nat`,
  `l2r_addr_int`: the boxed scalar when small, else its big number's
  pointer), the bits of a `UInt64` or `Float`, and a number answered only
  once (`l2r_addr_fresh`: even, in `[2^62, 2^63)`) for a value of a type
  `addrOf` does not know. For two values alive at the same time, equal answers
  mean the same cell or equal values; a value lean2rr converted to another
  representation is a new object.
- Everything runs on one thread, on lean-runtime's scheduler: tasks run
  when they are first needed, when the running code blocks, or when
  `main` returns (a schedule native Lean can produce; translation plan
  §5.14; lean-runtime's `docs/sched.md` lists its known differences).
  Contexts switch only when one blocks or at an effect or polling point
  (above; in a program that creates tasks every 1000th `ST.Ref` read is
  one, `refs`), a context that computes without these delays
  the others, and `IO.waitAny` does not pick the fastest of several
  unfinished tasks. Blocking system calls cooperate (a read of an empty
  pipe, a write to a full one, `flock`, `Child.wait` let the other
  contexts run); a few still block the program (`open` of a FIFO).
- Child processes: natively `Child.pid` leaks its argument (Lean passes
  the child owned, the C function treats it as borrowed), so the child's
  pipes are never closed after a `pid` call, and a child waiting for end of
  file on its stdin after `takeStdin` waits forever; lean2rr releases it
  as usual. A child is started with `posix_spawn` (lean-runtime: safe Rust
  cannot fork), its working directory entered by lean-runtime's spawner
  thread, a child that cannot start being a stand-in `/bin/sh` that prints
  Lean's message (lean-runtime's `io::process` documents each step and
  what remains different).
- `IO.getNumHeartbeats` is 0 (natively it counts small allocations);
  `dbgStackTrace` prints nothing.
- The `errno` reported by a handle's sticky error indicator (see file
  primitives) is lean-runtime's model of it, set by every failing call it
  models as the C call would; it may differ from native after unrelated
  failing calls (the runtime's own calls are not libc++'s).
- `IO.FS.createTempFile`/`createTempDir` with `TMPDIR` naming a missing
  directory report `no such file or directory` with an empty file name;
  natively `decode_uv_error` dereferences a null file name and crashes.
  The same crash happens natively whenever an error without a file name
  has errno `ENOENT` or `EINTR` (`getCurrentDir` after its directory was
  removed; `getLine` on a handle whose error indicator is set, after a
  failed `metadata` left `errno = ENOENT`); the runtime raises the class's
  error with an empty file name (`noFileOrDirectory "" 2 "no such file or
  directory"`, `interrupted "" 4 ...`) for every call that passes no name:
  `getcwd`, `waitpid`, `kill`, `flock`, and the handle primitives (`fflush`,
  `fseek`, `ftruncate`, `fread`, `fwrite`, getline, `fputs`). LB-03 in
  lean-runtime's docs/lean-bugs.md; plan §10, "Runtime: Lean bugs we do not
  reproduce"; test `RtErrorNoFileName`.

## Testing

`tests/runtime/run.sh [NAME...]` builds every `tests/runtime/Rt*.lean`
natively (`lean` + `leanc -O3 -DNDEBUG`, like Lake's release build) and
through lean2rr, runs both (`LEAN_BACKTRACE=0`, optional `NAME.args` and
`NAME.stdin`; `NAME.pipe` is a shell command line run instead, with `$BIN`
the program, for redirections and pipes), and compares stdout, stderr and
the exit code byte for byte. lean2rr itself runs with
`LEAN_ABORT_ON_PANIC=1`: a panic while translating fails the test even if
the program's output matches. `NAME.xfail` marks tests blocked by a lean2rr
request. `NAME.l2r.out` (`.err`, `.code`) marks an intended difference from
native, a Lean runtime bug that lean2rr does not reproduce (plan §10,
"Runtime: Lean bugs we do not reproduce") or another item of plan §10:
that stream of lean2rr's run is compared with the file, and native's with
`NAME.native.out` (`.err`, `.code`), so both sides stay pinned. `NAME.deps`
names companion modules (`tests/runtime/<name>.lean`, not named `Rt*`),
compiled before the test and linked into its native build, for programs of
several modules. A test's `NAME.ffi.c` is C code linked into its native build
only: the C side of the test's own `@[extern]` declarations, which lean2rr
never uses (it runs their Lean definitions, translation plan §5.8);
`NAME.refused` makes a refusal by lean2rr the expected outcome (each
line of the file in its output, or after `! ` not in it), and `NAME.l2r-log` lists lines lean2rr's
build output must (or, after `! `, must not) contain, such as its note on
which externs run their Lean definition. `tests/runtime/shim-types.sh`
checks that each `@[export]` definition of lean2rr's shim (`L2RShim`) has
the type of the `@[extern]` declaration of its C symbol (Lean pairs them by
name only). The Rust unit tests of `leanrt`
(bignums, one-word `Nat`/`Int` at the boundaries, tagged arrays, string
layout and counts, the last-error slot over lean-runtime's decoding) run
with
`tests/runtime/leanrt-unit.sh`; `tests/runtime/rows-check.sh` checks
lean-runtime's rows through a lean2rr build of its row oracle (an `LB-nn`
row, a Lean bug or limit lean2rr does not reproduce, against the
definition's result).
`tests/runtime/ffi-inline-check.sh` builds runtime tests to LLVM IR and
fails on a call through the FFI boundary (a texture not inlined) or a
`black_box` barrier inside Reussir code (an inlined `black_box`ed libm
function): either would keep a Lean loop's tail call.
`tests/runtime/wait-inline-check.sh` builds `RtWaitInline` to an executable
and fails when a fast path of lean-runtime's wait cores (a reference
point, a thunk's store or its `done_keyed`) is reached by a call or branch
in the functions that hold its loops, or a thread-local access is not
direct (TLS descriptor or module relocations).
`tests/runtime/nat-alloc-check.sh`
builds `RtNatStress` with leanrt's big-number counters and checks that
every big number made is freed exactly once. `tests/runtime/conv-count-check.sh`
builds the `RtUniformUpdates*` tests with lean2rr's
conversion counter (`L2R_COUNT_CONVERSIONS`: each generated conversion
counts the elements it rebuilds, printed at exit) and checks that they grow
at most linearly with the size (no container converted per update).
