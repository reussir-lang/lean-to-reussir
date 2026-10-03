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

- **What:** A module named `Init.*`, `Std.*`, `Lean.*` or `Lake.*` whose
  `.olean` is not under the toolchain's library directory is an error at
  load ("rename it").
- **Why:** lean2rr takes such modules for Lean's library (constants
  evaluated lazily, `initialize` actions run by the runtime, `unsafe` code
  trusted when deciding whether the program casts); a program module with
  such a name would silently be translated as a different program (round 6
  RV6T-06, 177b9be). Natively the name is allowed when the toolchain's
  module of that name is not imported (plan
  [§10](../translation-plan.md#10-known-divergences-and-unsupported-features)).
- **Where:** `LeanToReussir/Env.lean`: `loadEnvironment`;
  `LeanToReussir/CompileRecord.lean`: `isToolchainModule`.
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
  repros of Reussir bugs 16, 17 and 20), `L2R_DEBUG` prints whether the
  program can cast and why, and each declaration Stage 1 could not
  recompile from source, with the error. The driver reads `L2R_REUSSIR`,
  `L2R_RUSTC`,
  `L2R_GMP`, `L2R_LEAN2RR`, `L2R_DISABLE_OPTS`, `L2R_ENABLE_OPTS`,
  `L2R_RRC_FLAGS`.
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
