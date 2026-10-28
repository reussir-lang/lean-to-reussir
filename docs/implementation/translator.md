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
  need `Box` (its re-typing takes a `◾` argument as a placeholder, as
  Stage 3 does: `◾` arguments alone do not give a parameter a type);
  `--no-check` turns off Lean's checker between Stage 2's
  passes. `Nat` and `Int` have one representation, Reussir's built-in
  integers: `--int-backend rcgmp` is accepted and ignored, and
  `--int-backend leanrt` is refused (until D8, 2026-10-26, it selected
  leanrt's one-word encoding, the default until 2026-10-25). Reussir
  passes them as owned handles at type arguments of generic FFI functions
  (Reussir's local patch R2, which scripts/l2r.py requires;
  `--rcgmp-type-args` is accepted and ignored; until 2026-10-25 a lowering
  for measurements that did not use R2 kept them out of type arguments):
  [representations/nat-int.md](representations/nat-int.md#the-lowering).
  Environment switches: `L2R_NO_OUTLINE` and
  `L2R_NO_INLINE_ANCHORS` turn off two build-time workarounds (for the
  repros of three Reussir costs, fixed upstream in #672, #670 and #674,
  and of the inliner's copies into one function, `RtJpWide`),
  `L2R_ALLOW_MISSING_EXTERNS`
  turns the rejection of a program that reaches an extern lean2rr cannot
  serve into a warning (the generated program then does not build: a
  refused extern of the program is called as `l2r_refused_<declaration>`,
  checked by `tests/runtime/allow-missing-check.sh`;
  [externs-ffi/program-externs.md](externs-ffi/program-externs.md#refusals-are-reported-at-translation-with-the-reason)),
  `L2R_TIMINGS` prints one line per step of the pipeline on stderr
  (loading, Stages 1 to 3, the passes over mono code, the parts of the
  lowering, `Outline`, the release order at the start of a branch, the
  passes over the generated functions, rendering, writing):
  the wall time of the step, the time since the start, the resident memory
  now and at most (`VmRSS`, `VmHWM`), and a count of what the step made;
  the output does not change (`LeanToReussir/Timings.lean`: `timingMark`),
  `L2R_DEBUG` prints whether the
  program can cast and why, each declaration Stage 1 could not
  recompile from source, with the error, what the optimizations
  `unread-fields` and `unreached-decls` kept, and the functions that `inline-anchors` keeps out
  of rrc's inliner for their copies; with that optimization on,
  `L2R_UNREAD_FIELDS_WHY` prints, for each extern of the `Lean` package
  that kept code reaches, the chain of declarations and reasons that
  keeps it ([optional-passes.md](optional-passes.md#values-in-unread-fields-are-left-out-unread-fields)).
  The driver reads `L2R_REUSSIR`,
  `L2R_RUSTC`, `L2R_INT_BACKEND` (only to refuse `leanrt`),
  `L2R_GMP`, `L2R_LEAN2RR`, `L2R_DISABLE_OPTS`, `L2R_ENABLE_OPTS`,
  `L2R_RRC_FLAGS`, and `REUSSIR_FFI_CACHE_DIR`, which it sets for rrc
  unless given (rrc's texture cache, for a Reussir cost:
  [reussir-workarounds/build-time.md](reussir-workarounds/build-time.md#old-issue-35-cost-every-texture-was-compiled-again-on-every-build)).
- **Why:** Debugging aids; the switches keep the repros meaningful while
  the workarounds stay on by default.
- **Where:** `Main.lean`: `pipeline`, `run`, `parseArgs`, `usage`;
  `emitBase`, `dumpDecls`; `LeanToReussir/Dump.lean`;
  `LeanToReussir/Timings.lean`; `LeanToReussir/Env.lean`:
  `loadEnvironment` (the step between importing and the extension states);
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

### Questions about types are answered once per run

- **What:** The questions that the passes ask about a mono type or a
  constructor again and again keep their answers for the whole run:
  - whether a type may hold a resource with an observable release
    (`mayHoldResource`, `resourceTypeCache`, for `unread-fields`), also
    through closures, thunks and tasks (`mayHoldRelease`, one function with
    a table of its own, `releaseTypeCache`, for `flatten-structs`' type
    rule, the lowering of borrowed arguments, `keepsAt`, and the release
    order at a branch's start, all in a program that can cast, and for the
    resource flow analysis' question of which binders get a node,
    `ResourceFlow.mayCarry`, in a program that cannot; until 2026-10-27
    that was a copy with a table per run, which differed only on a
    proposition's inductive, which no mono binder has: bug hunt
    hunt-resflow, C3). It
    is a reachability through array elements and
    constructor fields with one visited set per question, as rule 4's
    `mayHoldFn`: each type is looked at once per question, a `true` is
    kept for the types on the path that found it, a `false` for every type
    the question visited;
  - rule 4's question whether a type may hold a function value
    (`mayHoldFn`): its reachability's answers (`holdsFn`) and its final
    answers (`holdsFnTop`), which the flow analysis asks again for every
    link it tries; walking the type each time (`hasFnTy`) cost about a
    second on a program importing `Cslib.Init`, and a second walk of a
    first fix of `RtErasedBoxedContainer` added 4 s there;
  - the field types of a constructor's layout (`layoutFieldTypes`,
    `layoutFieldCache`), and, in rule 4's flow analysis, the same fields
    normalized (`layoutFieldKeys`);
  - in rule 4's links through `Box` (`flowThroughBoxes`), what
    `boxShapeCompat` compares of each boxed and unboxed type (`boxShape`:
    a function type's skeleton, or the head, the number of arguments and
    whether it is an inductive) and the type's normalized form, once per
    type and not once per pair; `flowLinkK` is `flowLink` on normalized
    types;
  - the name of a module by index (`moduleNameAt`), read from the header's
    module list: Lean's `EnvironmentHeader.moduleNames` builds the array
    of all module names at each call, and lean2rr indexed it once per
    constant (`programCasts`' walk, `isToolchainDecl`) and once per module
    in loops over the modules.
- **Why:** Translation time (2026-10-26, `L2R_TIMINGS`; single runs, so
  indicative). A program that imports `Cslib.Init` and prints one line
  (translation only; it reaches externs of the `Lean` package that the
  runtime does not have) took 170 s and 4.87 GB: 52 s of the 76 s it
  spent lowering declarations went to the resource question (then a
  search along every simple path, a cycle cut on the path only, and no
  table), 8 s of `flatten-structs`' 10 s to its copy, whose table kept a
  `false` only at the top, and 25 s to rule 4's links through `Box` (the field types
  computed again for every link, each pair's types normalized and compared
  again). Now 84 s and 4.43 GB: the set of links held its own normalized
  copies of the two types of every link, which made the peak. The
  path searches were exponential in the size of a dense mutual block
  (eight inductives, each with a constructor per member: about 20 times
  longer per member, 41 s at seven, minutes at eight; a first table that
  kept a `false` only where the search below met no type above it on the
  path halved that); the reachability takes well under a second at nine
  (test `RtResDenseMutual`, eight members). The
  module names: lean-zip's compressor (bench Z01c) spent about 1.9 s in
  each of the three walks of `programCasts` (`unread-fields`,
  `flatten-structs`' resource flow, the lowering), nearly all of it
  building those arrays: 7.5 s, now 3.2 s; the Cedar benchmark (Z06t)
  11.3 s, now 8.8 s. The answers depend only on the type or constructor
  and on the environment, which only grows meanwhile (`flatten-structs`'
  tuples, the externs that `mod-pow2`, `prelude-int-ops` and
  `utf8-size-add` add), and one lean2rr process translates one program,
  so the output is byte-identical: all 714 programs of the runtime tests
  and the classic corpus that translate, and the programs above.
- **Where:** `Lower/Borrow.lean`: `resourceTypeCache`, `mayHoldResource`
  (test `RtResDenseMutual`), `releaseTypeCache`; `Opt/ResourceFlow.lean`:
  `mayCarry`;
  `Opt/Flatten.lean`: `Resources.holds`, `resourceExcluded`;
  `Opt/UnreadFields.lean`: `mayHoldRes`; `ErasedDomains.lean`:
  `layoutFieldCache`, `layoutFieldTypes`, `layoutFieldKeys`,
  `FlowState.fieldKeys`, `flowLink`, `flowLinkK`, `flowLinkFields`,
  `BoxShape`, `boxShape`, `boxShapeCompat`, `flowThroughBoxes`;
  `CompileRecord.lean`: `moduleNameAt` (used by `Mono.lean`,
  `Lower/Conv.lean`, `Emit/Startup.lean`, `Emit/Program.lean` and the
  optional passes).
- **Remove only if:** never. A new rule in one of these questions must
  keep the answer a function of the type (or constructor) and the
  environment, or leave its table. A question about types that can be
  recursive is answered by a reachability with a visited set (or by
  strongly connected components), never by a search along every path:
  that is exponential in a dense mutual block (`RtErasedDenseMutual` for
  `mayHoldFn`, `RtResDenseMutual` for `mayHoldResource`).

### Stage 3 and the lowering see only the declarations the roots reach

- **What:** After Stage 2 the optimization `unreached-decls` (on by
  default) drops the declarations with code that no code reaches from
  `main`, the error printer, the startup steps and the `IO.Error`
  builders, so Stage 3, the passes over mono code, the program analyses
  and the lowering never see them; `L2R_TIMINGS`' line `prune passes`
  counts what is left
  ([optional-passes.md](optional-passes.md#declarations-that-nothing-reaches-are-left-out-unreached-decls)).
- **Why:** Translation time (2026-10-26): about a fifth of Stage 2's
  declarations with code are left over by Lean's passes; the program
  that imports `Cslib.Init` and prints one line translated in 83.9 s,
  now 73.3 s (4.42 → 4.33 GB). Each step after Stage 2 costs per
  declaration, and so did the late functions (persist walks and helpers
  for the variants that only the dropped code registered: 7.6 → 0.9 s).
- **Where:** `Opt/UnreachedDecls.lean`; `Main.lean`: `pipeline`.
- **Remove only if:** the steps after Stage 2 cost nothing for a
  declaration nothing reaches.
