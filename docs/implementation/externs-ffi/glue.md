# Extern glue

Paths are relative to `lean2rr/LeanToReussir/` unless they start with
`runtime/`. Plan
[§5.8](../../translation-plan.md#58-externs-and-runtime-calls).

### Extern instances pass values in their storage type

- **What:** A value whose *declared* type is a type parameter `α` (the
  element of `Array.push`, or a trivial structure over `α` such as
  `[Inhabited α]`, which mono represents by its field) is passed and
  returned in `α`'s storage type: wrapped or unwrapped if that is an
  `ElemBox`, converted to or from its index for an enumeration (only for
  externs over arrays of `α`). Other parameters (an index) are passed as
  they are. Type arguments go through `toMonoTypeKeep` first (instance keys
  hold base-phase types).
- **Why:** Storage types exist because values cross into Rust; boxing
  every argument broke the index of `Array.get!Internal` (runtime requests
  3 and 4; 9346467).
- **Where:** `Lower/ExternCall.lean`: `lowerExternCall`;
  `Lower/Externs.lean`: `typeVarUses`; `LowerBase.lean`: `ArrayRepr`,
  `arrayStorage`, `arrayElemTy`.
- **Remove only if:** never.

### Generic prelude functions over values are instantiated at the value types

- **What:** A prelude function that is plain Reussir code (not an FFI
  import) and whose signature applies no generic type (`RVec<T>`,
  `LRef<T>`) is instantiated at the extern's value types and receives its
  arguments as they are; function values among them become Reussir
  closures. lean2rr finds these functions by reading the prelude; among
  them are those of `dbgTrace`, `dbgSleep`, `dbgStackTrace`, `panic` and
  `sorry`.
- **Why:** `dbgSleep` at `Nat` was instantiated at `ElemBox` while its
  `Unit → α` closure was passed unwrapped, and did not compile (runtime
  request 8, 51733b2).
- **Where:** `Emit/Program.lean`: `valueGenericPreludeFns`,
  `valueGenericClosureParams`; `Lower/ExternCall.lean`:
  `lowerExternCall`.
- **Remove only if:** never.

### Externs over Lean-defined types get glue or constructor callbacks

- **What:** Externs whose results mention Lean-defined types (`Ordering`,
  `List`, `Option`, `Prod`, `EST.Out`, `IO.FS.Stream`) get generated glue:
  a runtime helper that receives the generated constructors as arguments
  (nullary ones as values, others as closures: `String.compare`,
  `String.toList`, `String.get?`, `Float.frExp`, `IO.getEnv`), or a
  generated loop (`Array.mk`, `Array.toList`, `String.mk`), or generated
  code (`timeit`/`allocprof` run the action through the runtime;
  `Lean.Name.beq` as structural equality comparing the cached hash first;
  `ShareCommon.State.shareCommon` as its reference body `(a, s)`;
  `String.Slice` hash and order, `ByteSlice.beq`).
- **Why:** The runtime cannot name lean2rr's generated types; the glue is
  a single call (9dcc679, 7d41e36, 797dfaa, 863d8ca; runtime requests 5,
  22, 25, 28, 30).
- **Where:** `Lower/Externs.lean`: `ctorCallbackExtern`, `structEqFn`,
  `listFold`, `ctorValue`, `ctorFieldTys`; `Lower/ExternCall.lean`:
  `customExtern`; `Lower/LazyGlue.lean`: `sliceGlue?`.
- **Remove only if:** never.

### `BaseIO` externs that cannot fail use payload primitives

- **What:** A `BaseIO` extern whose symbol `lean_xxx` has a prelude
  primitive `l2r_xxx` calls it and wraps the result as the IO result
  (`EST.Out.ok` / `ST.Out`). Arguments, and for a non-generic primitive the
  result, are converted between the extern's mono types and the
  primitive's: a runtime object (a handle, a mutex, a promise) is `lcAny`
  in mono code (a `Box`), and the runtime's `LHandle` or `LPromise` for the
  primitive.
- **Why:** The runtime cannot build `EST.Out`; one convention for all
  infallible IO (runtime request 9; c7b3933, f87ea08).
- **Where:** `Lower/ExternCall.lean`: `lowerExternCall`;
  `Lower/Externs.lean`: `wrapIOResult`, `ioPayloadTy`;
  `Emit/Program.lean`: `lowerProgram` (`preludeRets`, `preludeParams`,
  parsed from the prelude's signatures).
- **Remove only if:** never.

### Fallible IO uses a last-error slot and Lean's own error builders

- **What:** A fallible IO primitive (files, file system, standard streams,
  processes) records its outcome in a global last-error slot; the glue
  turns it into `EST.Out.ok` with the payload converted (unit, a handle,
  `Metadata`, an array of `DirEntry`) or into `EST.Out.error e`, with `e`
  built by Lean's exported `lean_mk_io_error_*` builder for the kind the
  runtime reports, as `decode_io_error`: `l2r_io_finish(v, ok, err)` with
  the two cases as callbacks (`ioFinish`). The `IO.Process.output` glue
  checks in line instead (`ioCheck`), so a handle its continuation uses is
  released at its last use there. `IO.FS.Mode` is passed as its
  constructor index.
- **Why:** The runtime cannot build `IO.Error`; Lean's own builders give
  the exact messages (57187b2). The runtime decodes as Lean 4.34's
  `decode_uv_error_impl`: kind and details from libuv's code for the errno
  (`leanrt::fs::crt_to_uv`, then `uv_strerror`, not `strerror`), the errno
  as the code; libuv-based operations (`decode_uv_error`) store the
  positive errno (4.33: libuv's negated code).
- **Where:** `Lower/Externs.lean`: `fallibleIOGlue`, `fallibleIOPrim`,
  `ioFinish`, `ioCheck`, `ioErrorFn`, `ioErrorCtor`, `ioUserError`,
  `metadataOf`, `dirEntriesOf`; `Mono.lean`: `isFallibleIOSym`,
  `ioErrorBuilderSyms`, `ensureIOErrorBuilders`;
  `runtime/leanrt/src/fs.rs` (`errno`, `error_kind`, `error_details`,
  `crt_to_uv`; unit test `fs_tests.rs`, every errno against native Lean);
  `runtime/README.md` ("Fallible IO", the table of error kinds); tests
  `RtIOErrorDecode`, `RtFiles`.
- **Remove only if:** never.

### Standard streams live in cells, and diagnostics use the current stderr

- **What:** The current standard stream of each descriptor is kept in a
  cell slot, built on first use as a Lean `IO.FS.Stream` whose fields are
  the runtime's stream primitives; `IO.setStdout` & co. swap it and return
  the previous one. Every program defines `l2r_stderr_put`, which writes
  with the current stderr's `putStr`, for panics, `dbgTrace`, `timeit`
  and the runtime's own messages. Handles and the standard streams are
  models of glibc's `FILE`.
- **Why:** Natively the current streams are per thread, and diagnostics go
  through `io_eprintln` to the current stderr (runtime request 21,
  7d41e36). The `FILE` model makes buffering, positions and `errno`s
  native's (d2ae23d).
- **Where:** `Lower/Externs.lean`: `stdStreamFns`, `streamValue`,
  `streamField`, `streamFieldCall`, `stdContextFns`, `stderrPutFn`;
  `runtime/leanrt/src/io.rs`, `cfile.rs`. Per-task streams:
  [../tasks/scheduler.md](../tasks/scheduler.md#each-task-starts-with-the-processs-standard-streams).
- **Remove only if:** never.

### Child processes are glue over runtime primitives

- **What:** `IO.Process.spawn` flattens `SpawnArgs` for `l2r_proc_spawn`
  (the three `Stdio` indices packed into one word, the environment as
  three parallel arrays) and builds the `Child` with its two hidden fields
  (pid, `setsid`); `wait`, `tryWait` and `kill` read them, holding the
  child until the result is built (they borrow it natively); `takeStdin`
  returns the stdin field and a new `Child` with a boxed unit there.
  `IO.Process.output`'s own body is replaced by glue that reads stdout and
  stderr together to end of file (`l2r_proc_drain`), then applies
  `readToEnd`'s UTF-8 checks and `wait` in native order.
- **Why:** As `process.cpp` (runtime request 29, ef971b7). Lean's
  `output` reads stdout in a dedicated task while it reads stderr; tasks
  are deferred here, so a child filling the stdout pipe before closing
  stderr would block forever.
- **Where:** `Lower/Process.lean`: `processExtern`, `spawnCall`,
  `spawnedChild`, `structField`, `processOutputBody`; `Lower/Code.lean`:
  `lowerDecl` (the `IO.Process.output` case); `runtime/leanrt/src/proc.rs`.
- **Remove only if:** the runtime gets real threads (for `output`); the
  rest never.

### `Std.Sync` objects are runtime handles

- **What:** `BaseMutex`, `Condvar`, `BaseRecursiveMutex` and
  `BaseSharedMutex` are `LHandle`s and their externs payload primitives
  over `leanrt::sync`; everything else in `Std.Sync` (`Mutex`, channels,
  `Barrier`, …) is Lean code over these and promises.
- **Why:** Natively C++ objects in `mutex.cpp` (f87ea08).
- **Where:** `runtime/prelude.rr` (`l2r_io_basemutex_*`, `l2r_sync_*`);
  `runtime/leanrt/src/sync.rs`; locking rules:
  [../tasks/scheduler.md](../tasks/scheduler.md#locks-belong-to-threads-with-glibcs-and-libcs-rules).
- **Remove only if:** never.

### References, thunks, tasks and promises

- **What:** `ST.Prim` externs, thunk and task externs, and promise externs
  have their own glue.
- **Where:** [../representations/references.md](../representations/references.md),
  [../tasks/cells.md](../tasks/cells.md); `Lower/Externs.lean`: `refGlue`;
  `Lower/LazyGlue.lean`: `lazyExtern`; `Lower/Promises.lean`:
  `promiseExtern`.
- **Why/Remove only if:** see the linked entries.
