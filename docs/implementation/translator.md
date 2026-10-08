# lean2rr itself: loading, limits, switches

Special cases in how the translator loads a program and runs. Paths are
relative to `lean2rr/` unless they start with `scripts/`.

### Extension states are loaded without running initializers

- **What:** lean2rr imports the program and loads the imported state of
  every persistent environment extension itself, like
  `importModules (loadExts := true)` but without running the imported
  modules' `[init]` declarations.
- **Why:** With `loadExts`, importing runs the program's own `initialize`
  actions inside lean2rr (444a70a). Without any extension state, queries
  Lean's passes rely on (`isClass` for dictionary folding) silently answer
  `false` (9296805).
- **Where:** `LeanToReussir/Env.lean`: `loadExtensionStates`,
  `loadEnvironment`.
- **Remove only if:** Lean offers loading extension states without
  running initializers.

### Modules are imported at `private` level

- **What:** The program and its imports are imported at `private` level.
- **Why:** Only this level exposes every module's complete base-LCNF
  bodies; the default `exported` level replaces non-public bodies with
  opaque stubs.
- **Where:** `LeanToReussir/Env.lean`: `loadEnvironment`.
- **Remove only if:** never.

### Program modules named like Lean's library are rejected

- **What:** Every loaded module named `Init.*`, `Std.*`, `Lean.*` or
  `Lake.*` must be the module of that name in the library of the toolchain
  lean2rr is built with, and every module named `L2RShim.*` the one in the
  shim directory; otherwise loading stops ("rename it"). The check is by
  file identity, not path: the `.olean` and its `.olean.server` and
  `.olean.private` parts (lean2rr reads the private part) must each be the
  same file (one path, a symbolic or hard link) or have the same contents.
  The toolchain is the one lean2rr was built with (its sysroot recorded at
  build time), not the one `lean` or the working directory's
  `lean-toolchain` names. The shim directory (`L2R_SHIM_DIR`, set by the
  driver; else `lib/lean` next to lean2rr's `bin/`) is last on the search
  path and must hold `L2RShim.olean` and `L2RShim/Core.olean`, or loading
  stops naming it.
- **Why:** lean2rr takes such modules for Lean's library or its shim
  (constants evaluated lazily, `initialize` actions run by the runtime,
  `unsafe` code trusted when deciding whether the program casts); a
  program module with such a name would silently be translated as a
  different program (round 6 RV6T-06, 177b9be; `L2RShim.*` was not
  checked: dropped `initialize` actions, an "unreachable" panic, round 8
  RV8L-01, 782c92b). Comparing paths rejected the real library reached
  through hard links, or from a directory whose `lean-toolchain` names
  another Lean (RV8L-02, 782c92b). A missing shim failed only in rrc
  (RV8L-06), and a module whose private part differed was accepted
  (RV8L-07; both 694f9cf). Natively the name is allowed when the
  toolchain's module of that name is not imported (plan
  [§10](../translation-plan.md#10-known-divergences-and-unsupported-features),
  "Module names").
- **Where:** `LeanToReussir/Env.lean`: `toolchainSysroot`
  (`l2r_build_sysroot%`), `shimDir`, `sameFile`, `moduleDiff`,
  `reservedNames`, `shimModules`, `loadEnvironment`;
  `LeanToReussir/CompileRecord.lean`: `isToolchainModule`;
  `scripts/l2r.py` (`L2R_SHIM_DIR`). Test `tests/env/run.sh`.
- **Remove only if:** library modules are recognized otherwise than by
  name.

### Module names that are not identifiers

- **What:** A module name on the command line is read as dot-separated
  components, each as written or between `«` and `»`; the driver also
  takes a `.lean` file (the module is its file name, its `.olean` next to
  it, with an error saying how to compile it when missing or stale).
- **Why:** `lean -o rbtree-zipper.olean rbtree-zipper.lean` makes the
  module `rbtree-zipper`, which `String.toName` read as the anonymous name
  (Reussir's benchmark suite; 2acd465).
- **Where:** `Main.lean`: `parseModuleName`; `scripts/l2r.py`:
  `module_and_path`.
- **Remove only if:** never.

### lean2rr runs with a 1 GiB stack and no recursion limit

- **What:** The driver sets `LEAN_STACK_SIZE_KB` to 1 GiB for lean2rr
  (unless it is already set);
  lean2rr sets the stack of the threads Lean's runtime creates afterwards
  (task workers) to 64 MiB; `CoreM` runs without a heartbeat limit and with
  an effectively unlimited `maxRecDepth`.
- **Why:** Lean's passes recurse once per nested `let`, and the program's
  `maxRecDepth` is not in the `.olean`: any fixed limit rejects some
  program Lean compiled (a 60000-element list literal needs more than
  64 MiB; adv3 CN3-04, 125df0c). `LEAN_STACK_SIZE_KB` sizes every thread
  Lean's runtime creates: at 4 GiB, lean2rr reserved about 21 GB of address
  space and died under `ulimit -v 16000000` (ST4-10, cb79602); 1 GiB is
  the stack Lean's own compiler runs on (adv5 RF-4, 1b06c3f).
- **Where:** `scripts/l2r.py`: `main`; `Main.lean`: `workerStackSize`,
  `setThreadStackSize`, `main`; `LeanToReussir/Env.lean`: `runCoreM`.
- **Remove only if:** never.

### Checkpoints, statistics and switches

- **What:** `--emit base|inst|mono|externs|retyped|rr` stops after a stage
  and prints it: `inst`, `mono` and `retyped` as typed LCNF dumps, with
  every binder's type (Lean's printer omits them); `base` with Lean's
  printer; `externs` as a report of the externs called; `rr` as the program
  text. `--stats`
  runs a dry-run specializer that reports where the typed translation would
  need `Box`; `--no-check` turns off Lean's checker between Stage 2's
  passes. Environment switches: `L2R_NO_OUTLINE` and
  `L2R_NO_INLINE_ANCHORS` turn off two build-time workarounds (for the
  repros of Reussir issues 16, 17 and 20, costs), `L2R_ALLOW_MISSING_EXTERNS`
  turns the rejection of a program that reaches an extern lean2rr cannot
  serve into a warning (the generated program then does not build: a
  refused extern of the program is called as `l2r_refused_<declaration>`,
  checked by `tests/runtime/allow-missing-check.sh`;
  [externs-ffi/program-externs.md](externs-ffi/program-externs.md#refusals-are-reported-at-translation-with-the-reason)),
  `L2R_DEBUG` prints whether the
  program can cast and why, and each declaration Stage 1 could not
  recompile from source, with the error. The driver reads `L2R_REUSSIR`,
  `L2R_RUSTC`,
  `L2R_GMP`, `L2R_LEAN2RR`, `L2R_DISABLE_OPTS`, `L2R_ENABLE_OPTS`,
  `L2R_RRC_FLAGS`, and `REUSSIR_FFI_CACHE_DIR`, which it sets for rrc
  unless given (rrc's texture cache, Reussir issue 35, a cost:
  [reussir-workarounds/build-time.md](reussir-workarounds/build-time.md#issue-35-cost-every-texture-is-compiled-again-on-every-build)).
- **Why:** Debugging aids; the switches keep the repros meaningful while
  the workarounds stay on by default.
- **Where:** `Main.lean`: `pipeline`, `parseArgs`, `usage`;
  `emitBase`, `dumpDecls`; `LeanToReussir/Dump.lean`;
  `LeanToReussir/Stats.lean`, `Specialize.lean`, `Retype.lean`;
  `LeanToReussir/Emit/Program.lean`: `lowerProgram`, `externReport`;
  `LeanToReussir/Mono.lean`: `recompile`; `scripts/l2r.py`.
- **Remove only if:** n/a.

### The `.rr` printer appends to one string

- **What:** The printer threads one accumulator through expressions, arms
  and blocks.
- **Why:** Building each nested block's text and concatenating it into its
  parent's copied text once per nesting level: quadratic in the nesting
  depth (22ae719). The output is byte-identical.
- **Where:** `LeanToReussir/RR.lean`: `joinTo`, `Expr.renderHead` and the
  `renderTo` functions.
- **Remove only if:** never.

### Stage 4 finds emitted functions by name and keeps its emitted items unshared

- **What:** Stage 4's state (`LowerState`) keeps the position of each
  emitted function by name (`fnPos`, brought up to date lazily by
  `syncFnIndex`), and every "is helper X already emitted" check asks it
  (`hasFn`); a test build's conversion counter has a flag
  (`convTickEmitted`), and generated `[value]` structs a reverse map
  (`tupleKeys`). The other lists that grow with the program and are searched before
  each addition have a set or map beside them: `Box` variants
  (`boxVariantOf`), unboxing targets (`unboxTargetSet`,
  `fnUnboxTargetSet`), application functions
  (`fnApplySet`) and function-value conversions (`fnConvSet`); the lists
  keep the order the output follows.
  A function replaced by another of the same name leaves a tombstone
  (`fnTombstone`, `.raw ""`) where it was and the new one goes at the end
  (`replaceFn`); the tombstones are dropped when the program is assembled
  (`liveFns`), so the items come out in the order that removing the old
  function and appending the new one gave. The state is read with
  `getPart f` (`modifyGet fun s => (f s, s)`), not `(← get).f`, wherever
  the read is followed by an update. `structConv` takes a function out of `convsInProgress` once it is
  emitted. Each function name appears at most once among the functions
  in `fns` (tombstones aside): every generator asks `hasFn` or a cache of
  its own first, or uses a fresh name; `syncFnIndex` stops with an
  internal error on a second function of a name (review R9S2R-01).
- **Why:** Each lookup scanned the whole list and each addition copied
  it: quadratic in the number of items. A program that imports a large
  library emits over 100000 items (`import Batteries` and one `println`:
  about 160000; round 9 RV9S-02). The arrays were copied because the
  state was shared: Lean's compiler computes a pure projection of
  `(← get)` where it is used, and keeps the state alive (shared) until
  then, across later `modify`s. The output is byte-identical.
- **Where:** `LeanToReussir/LowerBase.lean`: `LowerState`, `getPart`,
  `fnTombstone`, `liveFns`, `syncFnIndex`, `hasFn`, `replaceFn`,
  `dropFns`, `lazyState`, `boxPayload`, `unboxFn`;
  `Lower/Conv.lean`:
  `structConv`, `countConversion`; `Lower/FnValues.lean`:
  `applyCall`, `fnConvFn`, `unboxFnFn`; `Lower/Finish.lean`:
  `finishPersistFns`; `Emit/Program.lean`: `lowerProgram`. Test
  `RtConvProbeRollback` (two casts whose conversions generate the same
  helpers inside unboxing functions). The rollback of a cast's probe
  (`boxCastConv`) is gone: no cast that `boxCastable` accepts registers a
  helper and then fails (review of rule 1, simplicity finding 1).
- **Remove only if:** never.
