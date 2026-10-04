# `L2RShim`: lean2rr's Lean library for externs

`lean2rr/L2RShim.lean` is a library of its own, built with lean2rr. Each
definition is exported under an extern's C symbol, so lean2rr, which
compiles an extern's `@[export]` implementation instead of calling the
runtime ([dispatch.md](dispatch.md#externs-that-lean-implements-in-lean-are-compiled-from-lean)),
compiles it with the program. Plan
[§5.8](../../translation-plan.md#58-externs-and-runtime-calls)
("`Std.Internal.UV`").

### `Std.Internal.UV` is implemented in Lean over the event loop

- **What:** Timers, TCP and UDP sockets, name resolution, signals,
  `Std.Net`'s address conversions and interfaces, and
  `Std.Internal.UV.System` are Lean code over primitives of the runtime's
  event loop (`leanrt::net`, `leanrt::sys`) that take and return plain
  values (numbers, strings, byte arrays, handles, promises). Each follows
  the C function of the same symbol (`src/runtime/uv/*.cpp`) check by
  check, with libuv's errors built as `lean_decode_uv_error` builds them
  (classified by libuv's code, `uv_strerror`'s message, and since Lean 4.34
  the positive errno as the code: `L2RShim.uvErrno`).
- **Why:** Natively these are C over libuv building Lean values
  (`IO.Promise`, `Except IO.Error …`, `SocketAddress`), which lean2rr's
  runtime cannot build (5021ddf, 470425c).
- **Where:** `lean2rr/L2RShim.lean` (`uvError`, `check`, `whenDone`,
  `addrResult`, `acceptResult`, …); `runtime/leanrt/src/net.rs`, `sys.rs`;
  `runtime/prelude.rr` (`l2r_shim_*`).
- **Remove only if:** the runtime builds Lean values, or links libuv and
  Lean's C code (see [c-ffi.md](c-ffi.md)).

### The shim is loaded with the program and treated as library

- **What:** The driver names lean2rr's build library directory in
  `L2R_SHIM_DIR`; lean2rr puts it last on the search path and always
  imports `L2RShim` with the program, stopping when the directory does not
  hold it. It counts as a toolchain module: no startup work, constants
  evaluated lazily, and its `unsafe`/`@[extern]`/`@[export]` declarations
  do not make a program one that can cast. A program module named
  `L2RShim.*` is rejected
  ([../translator.md](../translator.md#program-modules-named-like-leans-library-are-rejected)).
- **Why:** The shim is lean2rr's own trusted code, not the program's (RV6T
  fixes, 0d358d4). A wrong shim directory failed only in rrc (round 8
  RV8L-06, 694f9cf).
- **Where:** `Env.lean`: `shimDir`, `shimModules`, `loadEnvironment`;
  `CompileRecord.lean`: `isToolchainModule`; `scripts/l2r.py`:
  `SHIM_DIR`.
- **Remove only if:** never.

### Operations that complete later resolve through a `sync` continuation

- **What:** The shim gives the runtime a promise `r` of `Unit` with the
  operation and attaches a `sync` continuation to `r` that reads the
  operation's outcome and resolves the promise the program sees; the
  runtime drops `r` when the operation completes.
- **Why/Where:** see
  [../tasks/scheduler.md](../tasks/scheduler.md#the-event-loop-completes-operations-through-promises);
  `lean2rr/L2RShim.lean`: `whenDone`.
- **Remove only if:** see the linked entry.

### `IO.Promise.isResolved` is replaced (borrow-dependent behaviour)

- **What:** The shim exports `l2r_override_IO_Promise_isResolved`, which
  asks the runtime and then releases the promise; Stage 1 calls it instead
  of Lean's definition.
- **Why:** Natively `isResolved` borrows the promise (`result?` does), so
  the caller releases it after the question, and a last reference resolves
  the promise with `none` only then. Compiled as written, the release came
  inside `result?`, before the question, and `isResolved` on a promise's
  last use answered `true` (470425c).
- **Where:** `lean2rr/L2RShim.lean`: `promiseIsResolved`,
  `primPromiseIsResolved`; `runtime/leanrt/src/task.rs`:
  `promise_is_resolved`; `Mono.lean`: `redirectTarget`.
- **Remove only if:** Reussir gets borrowed parameters (or Lower/Borrow
  covers promises).

### Time, Windows time zones and `ShareCommon`

- **What:** `Std.Time.Timestamp.now` is the system clock in nanoseconds,
  split as `Duration.ofNanoseconds` splits it; the Windows-only time zone
  externs fail with `io.cpp`'s errors for other systems;
  `ShareCommon.Object.eq`/`hash` work by object identity.
- **Why:** Found by probing every `Init`/`Std` extern in a program of its
  own (a2b49cd). lean2rr's objects have no Lean layout to compare byte by
  byte, and `shareCommon` is the identity here.
- **Where:** `lean2rr/L2RShim.lean` (`lean_get_current_time`,
  `lean_windows_get_next_transition`,
  `lean_get_windows_local_timezone_id_at`, `lean_sharecommon_eq`,
  `lean_sharecommon_hash`); `runtime/leanrt/src/io.rs`: `realtime_nanos`
  (lean-runtime's `io::time::current_time`).
- **Remove only if:** never.

### System queries follow libuv's Linux code, with Lean's buffers

- **What:** `Std.Internal.UV.System` queries are lean-runtime's
  (`io::uvsys`, through `leanrt::sys`): they read what libuv reads
  (`/proc/uptime`, `/proc/stat` without its totals line, `/proc/meminfo`,
  cgroup v1/v2 memory limits, the password and group databases, …) with
  the buffers Lean passes
  (`UV_ENOBUFS` for a home or temporary directory of `PATH_MAX` bytes or
  more, a process title of 512 or more) and libuv's argument checks (a
  priority outside [-20, 19], `random` of more than `0x7FFFFFFF` bytes).
  `setProcessTitle` writes the title into the arguments' memory, so
  `/proc/self/cmdline` shows it (lean-runtime's feature `proc-title`), and
  reports libuv's error. A lean-runtime error reaches the shim as its libuv
  code (`sys::uv_code`: lean-runtime decodes with `decode_uv_error(code,
  name)`, which keeps `-code`), and the shim builds the same `IO.Error`
  (`uvError`, and the named variants of `chdir` and `osGetGroup`). Name
  resolution checks the host as libuv does (an empty host name or one of
  256 bytes or more is `EINVAL`, at once). Strings are decoded as
  `lean_mk_string`.
- **Why:** Round 6 IO findings (IO6-01..13, 15; 1362da1) and 024c024;
  one implementation for both translators (switch step 3; leanrt's own
  ports moved into lean-runtime).
- **Where:** `runtime/leanrt/src/sys.rs`; lean-runtime's
  `src/io/uvsys.rs`, `argv_title.rs`; `runtime/leanrt/src/net.rs`:
  `dns_get_info`; `lean2rr/L2RShim.lean` (the System section).
- **Remove only if:** never.
