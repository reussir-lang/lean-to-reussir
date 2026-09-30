# lean2rr runtime

The runtime has two parts:

- `prelude.rr` — Reussir source that lean2rr prepends to every generated
  program. It defines the runtime types and one function per Lean extern
  (`lean_xxx` for the extern whose C symbol is `lean_xxx`), plus `l2r_*`
  primitives for lean2rr-generated glue.
- `leanrt/` — a Rust crate (rlib) linked into every program. The prelude's
  `#[ffi(import)]` textures call into it. It holds the bignum code (GMP),
  string algorithms, float formatting, buffered stdio, files, once-cells,
  panics and the main-thread setup — and, being a single crate, the one copy
  of all global state (statics in the prelude's `extern "rust"` block would
  be duplicated per texture).

Semantics follow Lean 4.33's C runtime (`lean.h`, `src/runtime/*.cpp`)
exactly; comments at each function say which C function it mirrors.

Generated sections of the prelude (edit the generator, then run it):
`runtime/gen_scalars.py` (UIntN/IntN/USize/ISize) and
`runtime/gen_tagarr.py` (`Array Nat`/`Array Int`).

## Building and linking

`scripts/l2r.py` does everything:

1. builds `leanrt` with the pinned rustc (`L2R_RUSTC`) into
   `runtime/leanrt/target/libleanrt.rlib`, cached by a hash of its sources;
2. runs lean2rr (`L2R_LEAN2RR`) with `--prelude runtime/prelude.rr`;
3. runs rrc (`L2R_REUSSIR`; with `--reuse-across-call` unless `l2r.py` gets
   `--no-reuse-across-call`) with
   - `--polyffi-rust-path runtime/leanrt/target/rustc-native`: a wrapper that
     adds `-C target-cpu=native -C target-feature=-outline-atomics`. With the
     plain rustc, textures are not inlined into Reussir code, and calls through
     the packed-argument boundary (float or `str` arguments, four or more
     parameters) leave an escaping stack slot that blocks tail-call
     elimination: loops that print floats overflow the stack.
   - `--polyffi-libdir runtime/leanrt/target` (so textures find `leanrt`),
   - `--link-lib libleanrt.rlib --link-lib libgmp.a` (GMP from the Lean
     toolchain, `$(lean --print-prefix)/lib/libgmp.a`, or `L2R_GMP`).

## Representations

| Lean (mono) | Reussir | Notes |
|---|---|---|
| `Nat` | `enum [value] Nat { Small(u64), Big(LBig) }` | `Big` only for values `>= 2^64` |
| `Int` | `enum [value] Int { Small(i64), Big(LBig) }` | `Big` only outside the `i64` range |
| big numbers | `LBig` = `Rc<(bool, Vec<u64>)>` | sign, little-endian limbs, normalized; GMP `mpn`/`mpz` |
| `String` | `LStr` = `Rc<Vec<u8>>` | valid UTF-8, no terminator; copy-on-write |
| `Array α` | `RVec<E>` = `reussir_rt::collections::vec::Vec<E>` | `E` = storage type of `α` (lean2rr boxes non-boundary types) |
| `Array Nat`, `Array Int` | `LNatArr`, `LIntArr` | one tagged word per element (below) |
| `ByteArray`, `FloatArray` | `RVec<u8>`, `RVec<f64>` | `RVec<u8>` and `LStr` share a layout: `String.toUTF8` is free |
| `ST.Ref σ α` / `IO.Ref α` | `LRef<E>` (a shared 0/1-element vector) | mutated through every alias; empty after `take` |
| `IO.FS.Handle` | `LHandle` | shared buffered file, closed with its last reference |
| `UInt8..64`, `USize` | `u8..u64`, `u64` | |
| `Int8..64`, `ISize` | `u8..u64`, `u64` (bit patterns) | signed semantics as `lean_int8_*` etc. |
| `Char` | `u32` | |
| `Float`, `Float32` | `f64`, `f32` | |
| `Bool` | `bool` | |
| `Unit`, `PUnit`, erased | `L2RUnit` | `enum [value] L2RUnit { u }` |

Every function consumes its arguments (Reussir's convention). Strings,
arrays and big numbers are updated in place when uniquely referenced
(`Rc::is_unique`), otherwise copied once. Textures that only read a handle
release it through `leanrt::rc_release`/`array::release`, whose last-reference
drop is out of line; together with `#[inline(always)]` fast paths and
`#[cold]` slow paths this lets LLVM inline the hot textures (array
get/set/push/size, string get/next/push, the Nat helpers) into Reussir code
(checked with `rrc --emit llvm-ir`).

**`Array Nat`/`Array Int`.** `Nat`/`Int` are `[value]` enums, which cannot
cross the FFI boundary, so a generic `RVec` stores them in a heap box per
element (an allocation per update). `LNatArr`/`LIntArr` (`leanrt::tagvec`)
store one word per element instead, like Lean: `(v << 1) | 1` for small
values (`Nat` below 2^63, `Int` in [-2^62, 2^62)), a big-number handle
otherwise. Tagged words never reach Reussir code (Reussir increments opaque
handles inline, so a tagged scalar cannot be an opaque value). Every
`lean_array_xxx<E>` / `l2r_array_xxx<E>` has `lean_natarr_xxx` /
`l2r_natarr_xxx` (and `intarr`) with the same arguments and element type
`Nat` (`Int`); `lean_mk_array`/`lean_mk_empty_array_with_capacity` become
`lean_mk_natarr`/`lean_mk_empty_natarr_with_capacity`.

## Calling convention

As fixed by lean2rr:

- The extern `lean_xxx` is called as the prelude function `lean_xxx`, with
  the extern's mono-phase parameters in order minus erased ones (types,
  proofs, `lcErased`) and minus the IO world (`lcVoid`).
- Polymorphic externs take explicit storage type arguments:
  `lean_array_push<E>(arr, x)`.
- Functions whose results mention Lean-defined inductive types (`List`,
  `Option`, `Prod`, `Ordering`, `EST.Out`, ...) cannot be written here: the
  prelude offers primitives and generic helpers for lean2rr's glue (below).

Nat positions and indices: a `Nat::Big` value is never a valid position or
index. Where Lean's C code distinguishes "not a scalar" (`>= 2^63` in Lean)
from "out of range", the prelude reproduces that too
(`lean_string_utf8_extract`, `Float.scaleB` with Ints outside 32 bits).

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

**IO externs that cannot fail** (BaseIO) have a payload primitive named
`l2r_` + the symbol without `lean_`, taking the same passed arguments;
lean2rr wraps its result with `wrapIOResult`: `l2r_io_mono_ms_now()`,
`l2r_io_mono_nanos_now()`, `l2r_io_get_random_bytes(n)`,
`l2r_io_process_get_pid()`, `l2r_io_get_num_heartbeats()`,
`l2r_io_check_canceled()`, `l2r_io_get_tid()`, `l2r_io_initializing()`,
`l2r_io_set_heartbeats(n)`, `l2r_runtime_mark_persistent<T>(a)`,
`l2r_runtime_mark_multi_threaded<T>(a)`, `l2r_runtime_forget<T>(a)`,
`l2r_runtime_hold<T>(a)`, `l2r_io_prim_handle_is_eof(h)`,
`l2r_io_prim_handle_is_tty(h)`. (`l2r_io_app_path()`, `l2r_io_current_dir()`
and `l2r_io_process_get_current_dir()` are infallible stand-ins for the
fallible primitives below.) References: `l2r_ref_new/get/set/swap/take/ptr_eq`.

**Fallible IO** (files, standard streams): primitives record their outcome
in a global last-error slot; the glue is

    let v = l2r_fs_open(path, modeIndex);
    l2r_io_finish(v, |v| EST.Out.ok(v), |kind| |errno| |fname| |details| mkError)

where `mkError` builds the `IO.Error` with the `lean_mk_io_error_*`
constructor (exported Lean functions) numbered `kind`, as Lean's
`decode_io_error`:

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

The operations Lean implements with libuv (`removeFile`, `hardLink`,
`metadata`, `symlinkMetadata`, `createTempFile`, `createTempDir`) report
errors as `decode_uv_error`: the errno is libuv's negated errno as a
`UInt32` (`4294967294` for `ENOENT`), the details are `uv_strerror`'s, and
errnos libuv does not map are kind 0. Kind 23 is Lean's
`io_result_mk_error(msg)` (`IO.currentDir`, `IO.appPath`).

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
its path, for the `Handle × FilePath` pair), `l2r_fs_create_tempdir()`.
**stdio model.** Handles and the standard streams are models of glibc's
`FILE` (`leanrt/src/cfile.rs`, following libio's `fileops.c`/`genops.c`
function by function): one `st_blksize` buffer shared by reading and
writing with libio's get/put areas and cached offset; `fwrite`
(`_IO_new_file_xsputn`, line-buffered tails flushed at each newline),
`fread` (`_IO_file_xsgetn`, including direct reads of whole blocks),
`getc`, `fflush`, `fseek` (in-buffer seeks), `ftello`; `EBADF` for the
wrong direction after the same mode switch; sticky end-of-file and error
indicators (after any failed operation on a handle, `getLine` fails, as
natively); reading a terminal first flushes a line-buffered stdout. The
same system calls happen in the same order, so the `errno`s are native's.
At exit, stdout is flushed first (libc++'s `ios_base::Init`), then every
`FILE`'s pending output, newest first, then used streams are synced (a
seekable stdin is left at the position the program read up to).

Standard-stream primitives (`fd` = 0 stdin, 1 stdout, 2 stderr; the fields
of `IO.FS.Stream`): `l2r_stream_putStr(fd, s)`, `l2r_stream_write(fd, b)`,
`l2r_stream_flush(fd)`, `l2r_stream_read(fd, n)` and
`l2r_stream_getLine(fd)` record their outcome like the file primitives
(`EPIPE`, `EBADF` for the wrong direction, `EINVAL` on streams that were
closed at startup); `l2r_stream_isTty(fd)` cannot fail.

**Other glue primitives.**

| Lean | primitives |
|---|---|
| `initialize`, closed terms | once-cells `l2r_once_has(slot)`, `l2r_once_get<T>(slot)`, `l2r_once_set<T>(slot, v)` |
| `IO.setStdout`/`setStderr`/`setStdin` | a cell per stream: `l2r_once_*` plus `l2r_cell_swap<T>(slot, v) -> T` (returns the previous value) |
| `IO.Promise α` (as `LRef<E>`) | `l2r_promise_new<T>()`, `l2r_promise_resolve<T>(v, p)` (first wins), `l2r_promise_result_with<T, O>(p, none, some)`, `l2r_option_get_or_block_none<T>()` (`Promise.result!` of a dropped promise: Lean's message, then blocks) |
| `IO.getTaskState`, `IO.cancel` | `l2r_io_get_task_state_with<T, S>(t, waiting, running, finished)`, `l2r_io_cancel<T>(t)` |
| `timeit`, `allocprof` | `l2r_io_timeit_with<R>(msg, act)`, `l2r_io_allocprof_with<R>(msg, act)` |
| `Void.mk` | `lean_void_mk<T>(x)` |

**Main thread.** `leanrt::rt::run_main(|| body())` runs the program on a
thread with a 1 GiB stack and Lean's stack-overflow report (a fault in the
stack guard page prints `\nStack overflow detected. Aborting.` and aborts,
exit 134, without flushing stdout — as native).
`leanrt::rt::run_main2(|| init(), || body())` first runs `init` (the
module initializers) on the calling thread, as native `main` does. Both
put epoll descriptors in place of standard descriptors closed at startup
(native Lean's libuv descriptors take their place, so using them fails
with `EINVAL`), including the `/dev/null` Rust's runtime substitutes.
`l2r_set_initializing(b)` sets what `IO.initializing` answers.

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
7. `BaseIO.asTask` (symbol `lean_io_as_task`): the task glue is keyed on
   `IO.asTask`, which is not the 4.33 extern.
8. `dbgTrace` (and `dbgSleep`, `dbgStackTrace`, `Thunk.mk`) at a boxed `α`:
   the `PUnit → α` closure argument must be wrapped to return the box
   (`lean_dbg_trace<ElemBox>(msg, f : L2RUnit -> Nat)` does not type-check).
9. BaseIO payload primitives above (`IO.monoMsNow`, `IO.getRandomBytes`,
   ...) and the file protocol need `wrapIOResult` glue; `IO.FS.Handle`
   (`lcAny` in mono code) must be represented as `LHandle`.
10. Externs implemented by `@[export sym]` Lean code (all
    `Substring.Raw.Internal.*`, many `String.Internal.*`,
    `lean_array_to_list_impl`, `IO.eprint(ln)`, `lean_stream_of_handle`, the
    `IO.Error` constructors, `Lean.Name.beq` has a reference body) should
    compile and call that code; the prelude has hand-written versions of the
    `String.Internal.*` ones.
11. `Array Nat`/`Array Int` as `LNatArr`/`LIntArr` (names above).
12. `Nat.repr`/`Int.repr` of big numbers are Lean code dividing by 10 digit
    by digit (quadratic); `l2r_nat_repr`/`l2r_int_repr` are exact
    replacements using GMP.
13. *done* — The generated entry should run `l2r_main_body` through
    `leanrt::rt::run_main(|| unsafe { l2r_main_body() })` instead of its
    own `std::thread` (Lean's stack size incl. `LEAN_STACK_SIZE_KB` and
    `LEAN_MAIN_USE_THREAD`, and Lean's stack-overflow message; test
    `RtStack`).
14. *done* — The standard-stream glue should check each `l2r_stream_*` call with
    `l2r_io_finish`, as for files (tests `RtBrokenPipe`, `RtClosedStreams`).
15. *done* — `lean_io_prim_handle_is_tty` and `lean_io_prim_handle_is_eof` are
    `BaseIO`: the `lean_io_prim_handle_` prefix rule sends them to the
    fallible glue, which rejects them ("IO result ... cannot fail"). Use the
    BaseIO payloads `l2r_io_prim_handle_is_tty`/`_is_eof` (test
    `RtHandleIsTty`).
16. `ST.Prim.Ref.take` is lowered to `l2r_ref_get`, so the value stays in
    the cell and the taken copy is shared: every `modify`/`modifyGet`
    copies the array or string it updates (quadratic loops). Map it to
    `l2r_ref_take`.
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
21. Once `setStderr` is supported: native `panic!` (outside
    `LEAN_ABORT_ON_PANIC`, including the runtime's own panics such as
    `index out of bounds`), `dbgTrace`, `timeit` and `allocprof` print to
    the *current* stderr stream (`io_eprintln`); the runtime prints them to
    descriptor 2. Internal panics, uncaught exceptions and abort-mode panics
    do go to descriptor 2 natively. Needed from lean2rr: define in every
    program `fn l2r_stderr_put(s : LStr) -> u64`, writing `s` with the
    current stderr stream's `putStr` and ignoring its result (when the
    stderr cell is unset: `l2r_stream_putStr(2, s)`). The prelude may call
    functions defined after it, so the runtime then sends each diagnostic
    line (with its `\n`) through it.
22. *done* — `String.mk`/`List.asString` (`lean_string_mk`) take a `List Char`: glue
    folding the list with `lean_string_push` onto `lean_mk_string("")`.
23. `IO.initializing` is true while module initializers run (native
    `g_initializing` until `lean_io_mark_end_initialization`): the entry
    should call `l2r_set_initializing(true)` before the initializers and
    `l2r_set_initializing(false)` after (test `RtInitializing`).
24. Native `main` runs the module initializers on the process's main thread
    (8 MiB stack) and only `main` on Lean's big thread: the entry should be
    `leanrt::rt::run_main2(|| init(), || body())`, which runs `init` on the
    calling thread (with the stack-overflow report) and then `body` as
    `run_main` (test `RtInitStack`: a deep initializer overflows natively).
    An initializer's uncaught error prints `uncaught exception: ...` and
    exits 1 without running `main`, as natively.
25. `IO.getEnv` (`lean_io_getenv`) is emitted as a direct call to
    `lean_io_getenv`, which the prelude cannot define (its result is
    `Option String`); use `l2r_io_getenv_with(name, none, some)`.

For Reussir: `[value]` records across the FFI boundary would let arrays
store `Nat`/`Int`/enum-like values directly; and `mi_free` takes mimalloc's
generic path (`mi_free_generic_local`, `_mi_page_ptr_unalign`) for most
frees in allocation-heavy loops (30% of an array-update benchmark).

## Known divergences from native Lean

- Native `lean_string_utf8_extract` returns its borrowed string without a
  reference when a position is `>= 2^63`: a use-after-free natively. The
  prelude returns the string (the intended semantics).
- Panics print `backtrace:` and `(stack trace unavailable)` instead of a
  stack trace (unless `LEAN_BACKTRACE=0`, which prints neither, as native).
- Sharing is not observable: `isExclusiveUnsafe` answers `false`,
  `ptrAddrUnsafe` is the handle pointer (or the value's bits for scalars).
- Tasks run eagerly (promises are resolved before they are read);
  `IO.Process.spawn`, sockets, `Std.Sync` and timers are not implemented.
- `IO.getNumHeartbeats` is 0 (natively it counts small allocations);
  `dbgStackTrace` prints nothing.
- Huge `Array.mkEmpty`/`ByteArray.emptyWithCapacity` capacities are checked
  as natively (overflow panic; `out of memory` when `malloc` of the full
  size fails) but only `2^24` elements are reserved.
- The C `errno` reported by a handle's sticky error indicator (see file
  primitives) is the current `errno`, which may differ from native after
  unrelated failing calls (the runtime's own calls are not libc++'s).
- `IO.FS.createTempFile`/`createTempDir` with `TMPDIR` naming a missing
  directory report `no such file or directory` with an empty file name;
  natively `decode_uv_error` dereferences a null file name and crashes.
- A direct `read` of a huge count (`Handle.read`, ≥ one buffer) is issued in
  `read(2)` calls of at most 16 MiB (the same data; natively one call).

## Testing

`tests/runtime/run.sh [NAME...]` builds every `tests/runtime/Rt*.lean`
natively (`lean` + `leanc -O3 -DNDEBUG`, like Lake's release build) and
through lean2rr, runs both (`LEAN_BACKTRACE=0`, optional `NAME.args` and
`NAME.stdin`; `NAME.pipe` is a shell command line run instead, with `$BIN`
the program, for redirections and pipes), and compares stdout, stderr and
the exit code byte for byte. `NAME.xfail` marks tests blocked by a lean2rr
request. The Rust unit tests of `leanrt` (bignums, tagged arrays, hashes,
and a differential test of the `FILE` model against glibc's own `FILE`
over random operation sequences) run with `tests/runtime/leanrt-unit.sh`.
