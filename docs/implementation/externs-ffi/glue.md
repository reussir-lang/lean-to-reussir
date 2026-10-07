# Extern glue

Paths are relative to `lean2rr/LeanToReussir/` unless they start with
`runtime/`. Plan
[§5.8](../../translation-plan.md#58-externs-and-runtime-calls).

### Extern instances pass values in their storage type

- **What:** A value whose *declared* type is a type parameter `α` (the
  element of `Array.push`, or a trivial structure over `α` such as
  `[Inhabited α]`, which mono represents by its field) is passed and
  returned in `α`'s storage type: a `Box` when the extern stores `α`'s
  values as array elements (its *declared* signature has `Array α`, as
  `Array.push`: an array holds `Box`es, boxed going in, unboxed coming
  out, O(1)), and for any other `α` its own type, wrapped or unwrapped if
  that is an `ElemBox` (`cellStorage`). The choice is per type parameter,
  from the declared signature: `dbgTraceIfShared` at `α := Array Nat`
  passes the array itself. Other parameters (an index) are passed as they
  are. Type arguments go through `toMonoTypeKeep` first (instance keys
  hold base-phase types).
- **Why:** Storage types exist because values cross into Rust; boxing
  every argument broke the index of `Array.get!Internal` (runtime requests
  3 and 4; 9346467). The choice was once made for the whole extern, from
  its instantiated types: any extern instantiated at an array type boxed
  its `α` arguments, so `dbgTraceIfShared` on an array looked at a new box
  (never shared) and each call allocated a cell (correctness review of
  rule 1, finding 1; test `RtDbgShared`; the shared-check textures now
  read the count of a leanrt array or cell, `leanrt::drop::`, too).
- **Where:** `Lower/ExternCall.lean`: `lowerExternCall`;
  `Lower/Externs.lean`: `typeVarUses`, `typeVarsInArrays`;
  `LowerBase.lean`: `cellStorage`, `elemBoxOf?`; `runtime/prelude.rr`:
  `lean_dbg_trace_if_shared`, `l2r_shared_check`.
- **Remove only if:** never.

### Glue gets every value parameter of the declaration, erased or not

- **What:** The glue of an extern (`customExtern`, `refGlue`) reads its
  arguments by position. It gets each parameter that the extern's
  declaration does not erase (not a type argument, not a proof), the
  world included. A parameter that the instance erases but the
  declaration does not (`Task.pure`'s `a : α` at `α := Type`,
  `Thunk.mk`'s `Unit → α` at `α := Prop`) gets the value that Lean
  passes: `box(0)`, at the declaration's mono type, and for a function
  type a function that gives `box(0)`. Natively such a closure is
  `box(0)`, and `lean_apply_n` of a scalar gives the scalar, so a body
  that the instance erases never runs.
- **Why:** The glue got only the parameters that the instance does not
  erase: `Task.pure Nat`, `Thunk.mk fun _ => n = 3` and
  `Task.spawn fun _ => Nat` stopped the translation (`index out of
  bounds`, then a type error in rrc), and `ptrAddrUnsafe` of a type had
  no glue (the program was refused; test `RtExternErasedValue`).
- **Where:** `Lower/ExternCall.lean`: `lowerExternCall`,
  `genericParamTypes`, `erasedArg`.
- **Remove only if:** the glue stops reading arguments by position.

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

### Glue builds a payload at its own type, then boxes it into the result

- **What:** The fields of a generic type's parameter type are `Box`es (one
  type per inductive), among them the value of every IO result
  (`EST.Out.ok`, `ST.Out`), the error of `EST.Out.error`, a list's head
  and an `Option`'s value. Glue that builds or reads such a value works at
  the value's own type, taken from the extern's Lean type
  (`ioPayloadType`: `α` of `EST.Out ε σ α`; the components of a `Prod`,
  the tasks of a `List (Task α)`, the `Option String` of a process
  environment pair, `IO.FS.Stream`'s field types, `IO.Error`), and boxes
  it into the field (`wrapIOResult v vt`, `coerce`) or unboxes it from
  there: O(1), nothing is copied. `listFold` unboxes each head to the
  element type its step takes.
- **Why:** Glue that took the type to build from the result's field got a
  `Box` and stopped (metadata, directory entries, temporary files,
  `getEnv`, the standard streams, `asTask`, `mapTask`, `bindTask`,
  `waitAny`, `getTaskState`, `spawn`, `tryWait`, `takeStdin`,
  `IO.Process.output`), and a `Unit` payload was boxed as the `u64` the
  primitive returns.
- **Where:** `Lower/Externs.lean`: `ioPayloadFieldTy` (the field),
  `ioPayloadExpr?`, `ioPayloadType`, `ioErrorTy`, `wrapIOResult`,
  `ioFinish`, `streamPayloadTy`; their callers in `Lower/ExternCall.lean`,
  `Lower/LazyGlue.lean`, `Lower/Process.lean` and `Lower/Promises.lean`.
- **Remove only if:** never.

### `BaseIO` externs that cannot fail use payload primitives

- **What:** A `BaseIO` extern whose symbol `lean_xxx` has a prelude
  primitive `l2r_xxx` calls it and wraps the result as the IO result
  (`EST.Out.ok` / `ST.Out`). Arguments, and for a non-generic primitive the
  result, are converted between the extern's mono types and the
  primitive's: a runtime object (a handle, a mutex, a promise) is `lcAny`
  in mono code (a `Box`), and the runtime's `LHandle` or `LPromise` for the
  primitive. A generic primitive (`Runtime.markPersistent`,
  `markMultiThreaded`, `forget`, `hold`:
  `fn l2r_runtime_mark_persistent<T>(a : T) -> T`,
  `fn l2r_runtime_forget<T>(a : T) -> L2RUnit`) gets its arguments as
  they are. Its result has the type of the argument declared at the
  result's type parameter (`preludeRetArg`), or the prelude's result type
  (`L2RUnit`). The result field of the IO result is a `Box` (rule 1), so
  `wrapIOResult` boxes the result (test `RtRuntimeMarks`).
- **Why:** The runtime cannot build `EST.Out`; one convention for all
  infallible IO (runtime request 9; c7b3933, f87ea08). A generic
  primitive's result was taken to be of the field's type, so with rule 1
  rrc rejected every call of the four externs (`expected 'LAny', found
  'LStr'`).
- **Where:** `Lower/ExternCall.lean`: `lowerExternCall`;
  `Lower/Externs.lean`: `wrapIOResult`, `ioPayloadFieldTy`;
  `Emit/Program.lean`: `lowerProgram` (`preludeRets`, `preludeParams`,
  parsed from the prelude's signatures), `genericRetParams`
  (`preludeRetArg`).
- **Remove only if:** never.

### Fallible IO uses a last-error slot and Lean's own error builders

- **What:** A fallible IO primitive (files, file system, standard streams,
  processes) records its outcome in a last-error slot, each context's
  own (one static, which the scheduler glue's `switched` exchanges with
  the arriving context's at each switch: hunt HCO-01); the glue
  turns it into `EST.Out.ok` with the payload converted (unit, a handle,
  `Metadata`, an array of `DirEntry`) or into `EST.Out.error e`, with `e`
  built by Lean's exported `lean_mk_io_error_*` builder for the kind the
  runtime reports, as `decode_io_error`: `l2r_io_finish(v, ok, err)` with
  the two cases as callbacks (`ioFinish`). The `IO.Process.output` glue
  checks in line instead (`ioCheck`), so a handle its continuation uses is
  released at its last use there. `IO.FS.Mode` is passed as its
  constructor index.
- **Why:** The runtime cannot build `IO.Error`; Lean's own builders give
  the exact messages (57187b2). The decoding is lean-runtime's
  (`io::error`), as Lean 4.34's `decode_uv_error_impl`: kind and details
  from libuv's code for the errno (`crt_to_uv`, then `uv_strerror`, not
  `strerror`), the errno as the code; libuv-based operations
  (`decode_uv_error`) store the positive errno (4.33: libuv's negated
  code). leanrt's slot takes lean-runtime's `IoError` apart into the
  builder number (`fs::kind_of`), the code, the file name and the details
  (switch step 3). The slot is each context's own because a primitive
  can switch contexts after its `record`: when it releases a handle's
  last reference, the close waits for the handle's writer thread (the
  drain-end hook, switch step 14) while the other contexts run.
- **Where:** `Lower/Externs.lean`: `fallibleIOGlue`, `fallibleIOPrim`,
  `ioFinish`, `ioCheck`, `ioErrorFn`, `ioErrorCtor`, `ioUserError`,
  `metadataOf`, `dirEntriesOf`; `Mono.lean`: `isFallibleIOSym`,
  `ioErrorBuilderSyms`, `ensureIOErrorBuilders`;
  `runtime/leanrt/src/sched.rs` (`switched`);
  `runtime/leanrt/src/fs.rs` (`LastError`, `swap_last`, `set_err`, `kind_of`, `errno`, `error_kind`,
  `error_details`; unit test `fs_tests.rs`, every errno through the slot
  against native Lean);
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
  lean-runtime's models of glibc's `FILE` (`io::cfile`).
- **Why:** Natively the current streams are per thread, and diagnostics go
  through `io_eprintln` to the current stderr (runtime request 21,
  7d41e36). The `FILE` model makes buffering, positions and `errno`s
  native's (d2ae23d). The cells stay lean2rr's, not lean-runtime's
  `io::streams` (which keeps a translator's Rust values): the streams are
  lean2rr's own records of closures, and `IO.println` reads the current
  stdout at each call, inline (switch step 3).
- **Where:** `Lower/Externs.lean`: `stdStreamFns`, `streamValue`,
  `streamField`, `streamFieldCall`, `stdContextFns`, `stderrPutFn`;
  `runtime/leanrt/src/io.rs`; lean-runtime's `src/io/handle.rs`,
  `cfile.rs`. Per-task streams:
  [../tasks/scheduler.md](../tasks/scheduler.md#each-task-starts-with-the-processs-standard-streams).
- **Remove only if:** never.

### A Lean array the runtime reads is an array of boxes, read in place

- **What:** A runtime primitive that takes a Lean `Array T` (T not
  `UInt8` or `Float`) takes the one array type, `RVec<LAny>`, and reads
  each element in place from its box: the sends of the network shim
  (`Array ByteArray`: `l2r_shim_tcp_send`, `l2r_shim_udp_send`,
  `leanrt::any::bytes_ref`) and a spawn's arguments (`SpawnArgs.args :
  Array String`: `l2r_proc_spawn`, `l2r_proc_output`,
  `leanrt::any::str_ref`). `box(0)` reads as empty (the placeholder of
  the element type). Arrays the glue builds for a primitive from other
  Lean data (a spawn's environment as three parallel arrays, a
  directory's names) keep their own element types.
- **Why:** One representation per `Array α` (rule 1). A primitive declared
  over `RVec<RVec<u8>>` had no conversion from `RVec<LAny>`: every TCP and
  UDP send hit the "no representation conversion" panic (ef4a84a; RtTcp,
  RtUdp). A spawn's arguments were copied into an `RVec<LStr>` element by
  element (`l2r_proc_args_…`), a copy per spawn that native's
  `lean_io_process_spawn` does not make.
- **Where:** `runtime/prelude.rr`: `l2r_shim_tcp_send`,
  `l2r_shim_udp_send`, `l2r_proc_spawn`, `l2r_proc_output`;
  `runtime/leanrt/src/any.rs`: `bytes_ref`, `str_ref`;
  `runtime/leanrt/src/net.rs`: `Bufs`; `runtime/leanrt/src/proc.rs`:
  `with_args`; `Lower/Process.lean`: `spawnCall`.
- **Remove only if:** never.

### Child processes are glue over runtime primitives

- **What:** `IO.Process.spawn` flattens `SpawnArgs` for `l2r_proc_spawn`
  (the three `Stdio` indices packed into one word, the environment as
  three parallel arrays) and builds the `Child` with its two hidden fields
  (pid, `setsid`); `wait`, `tryWait` and `kill` read them, holding the
  child until the result is built (they borrow it natively); `takeStdin`
  returns the stdin field and a new `Child` with a boxed unit there.
  `IO.Process.output`'s own body is replaced by one primitive,
  `l2r_proc_output` (lean-runtime's `io::process::output`: stdout and
  stderr read together to end of file, `readToEnd`'s UTF-8 checks and
  `wait` in native order), and `l2r_proc_output_str` for the two outputs.
  The runtime keeps lean-runtime's process object of each child by pid
  until the child is reaped (`runtime/leanrt/src/proc.rs`).
- **Why:** As `process.cpp` (runtime request 29, ef971b7). Lean's
  `output` reads stdout in a dedicated task while it reads stderr (which
  lean-runtime's scheduler also runs: its pipe reads cooperate), and writes
  all of a `some` input before it reads the outputs, so a child that fills
  a pipe while it reads its input and the program wait for each other for
  good (LB-40). `l2r_proc_output` reads both pipes together and writes the
  input meanwhile. (The replacement first came because lean2rr's deferred
  tasks blocked Lean's pattern for good, before lean-runtime's IO
  cooperated.)
- **Where:** `Lower/Process.lean`: `processExtern`, `spawnCall`,
  `spawnedChild`, `structField`, `processOutputBody`; `Lower/Code.lean`:
  `lowerDecl` (the `IO.Process.output` case); `runtime/leanrt/src/proc.rs`;
  lean-runtime's `src/io/process.rs`.
- **Remove only if:** never (without the `output` replacement LB-40 comes
  back).

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
