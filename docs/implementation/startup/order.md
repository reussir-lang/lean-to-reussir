# What runs at startup, and in which order

Paths are relative to `lean2rr/LeanToReussir/`. Plan
[§2.2](../../translation-plan.md#22-reachability) and
[§5.12](../../translation-plan.md#512-constants-cafs-and-closed-terms).

### Every constant of the program is a root

- **What:** Stage 1 starts from `main`, `IO.Error.toString` (the entry
  point prints uncaught exceptions with it), the library's initializers
  (below, "The library's initializers run at their module's place,
  always"), and every
  startup item of the program's modules: each zero-parameter declaration
  of the module's compiled code (instances and compiler-generated
  specializations included), each `initialize` action and each init
  function of an `initialize` constant.
- **Why:** Natively a module's initializer evaluates all of these, used or
  not (fc23313). Consequence: an unused constant that reaches an extern
  the runtime lacks (or an extern of the program that lean2rr refuses)
  makes lean2rr reject the program (plan
  [§10](../../translation-plan.md#10-known-divergences-and-unsupported-features),
  "Not supported"). The exception, with the optimization `unread-fields`
  (off by default): a constant's closed terms that only feed fields no
  kept code reads are not evaluated (the constant itself still is), so a
  `panic!` or `dbg_trace` in them does not show
  ([../optional-passes.md](../optional-passes.md#values-in-unread-fields-are-left-out-unread-fields)).
- **Where:** `Emit/Startup.lean`: `startupItems`, `StartupItem`;
  `Emit/Entry.lean`: `entryRoots`, `programRoots`.
- **Remove only if:** never.

### Modules follow the module system's phases

- **What:** Modules are initialized in a depth-first post-order walk of
  the import graph from `main`'s module. When `main`'s module is a
  `module`, only runtime phases run: the walk follows only non-`meta`
  imports, and declarations marked `meta` are skipped. Otherwise every
  import is followed, and an imported `module` runs its runtime-phase
  items, then its `meta` ones. An item counts as `meta` when the
  declaration native Lean initializes is marked so (for
  `initialize c : T ← act`, `c`; for `initialize do …`, its function);
  compiler-generated declarations are not.
- **Why:** As `EmitC.emitMainFn`/`emitInitFn`/`emitLegacyInitFn`. lean2rr
  ran every item of every program module: `meta initialize`, `meta def`
  constants and meta-imported modules ran, and a failing compile-time-only
  initializer aborted the program (round 7 RV7O-01, 8727838; test
  `RtStartMeta`).
- **Where:** `Emit/Startup.lean`: `startupModules`, `importPostOrder`,
  `startupItems`.
- **Remove only if:** never.

### Declarations follow Lean's compilation order

- **What:** Within a module, items are first ordered by the program's
  structure (a `def`/`instance` command with its `where`/`let rec`
  helpers, compiled by strongly connected component, callees first; a
  specialization right before the component it was made in; elaboration
  auxiliaries before the whole command), rebuilt from declaration ranges,
  the kernel's `all`, macro scopes and names (numbers compared by value).
  Then the items that the `.olean` records an order for are put in
  compilation order, in the places the structure gave them: the module's
  `extraConstNames` (closed terms, `_boxed` wrappers, lifted lambdas,
  specializations) are listed newest first, and `compileOrder` reverses
  them. Every item the record does not place keeps its place, except that
  it goes after the constants it reads.
- **Why:** Native Lean initializes a module's declarations in the order it
  compiled them, and an initializer that traces or panics shows it. Each
  rule fixed an observed order: helpers by component and specializations
  in `initialize` actions (adv3 CN3-02/03, 448f92d), specializations before
  their block (adv2 PRG-10, af32ffd), equal ranges (adv4 ST4-01..04,
  e08b1d0), the recorded order (1042bed), `@[init f]` with an ordinary `f`
  and constants without a record (036d007).
- **Where:** `Emit/Startup.lean`: `moduleStartupKeys`, `declOrder`,
  `rangeKey`, `posLt`, `natStrLt`, `natNameLt`, `startupNameLt`,
  `specTarget?`, `isGeneratedInitFn`; `Collect.lean`: `nameOfComponents`;
  `CompileRecord.lean`: `compileOrder`, `compiledOwner`.
- **Remove only if:** never. What no rule recovers (members of a `mutual`
  block that do not use each other, made-up names of one quotation) is a
  known divergence (plan
  [§10](../../translation-plan.md#10-known-divergences-and-unsupported-features),
  "Startup order of unrecorded constants").

### Hygienic names keep their macro scopes at the end

- **What:** Name prefixes are rebuilt component by component, and a
  hygienic name's macro scopes stay at its end (`zz._closed_0._@.M._hyg.3`
  is a closed term of `zz._@.M._hyg.3`). A specialization of a hygienic
  declaration has them in the middle
  (`helper._@.M._hyg.3._at_.runIt.spec_1`); its origin, the part before
  `_at_`, is rebuilt the same way (`helper._@.M._hyg.3`).
- **Why:** `Name.append` reinterprets the macro scopes of a hygienic
  component and panicked on a prefix ending in `_hyg`: lean2rr printed
  "unreachable @ extractMainModule" for any macro-made declaration (round
  6 RV6L-04, 40ebf2c), and for any specialization of one, from
  `specOrigin?` via `isMapLoop`, with a wrong origin
  `helper.«_@».M.3` (round 9 RV9S-01; test `RtHygSpecName`, which
  `tests/runtime/run.sh` translates with `LEAN_ABORT_ON_PANIC=1`, so any
  lean2rr panic fails a runtime test).
- **Where:** `Collect.lean`: `nameOfComponents` (shared);
  `Mono.lean`: `specOrigin?`; `Emit/Startup.lean`: `specTarget?`;
  `CompileRecord.lean`: `compiledOwner`, `closedTermOwner?`;
  `Lower/Conv.lean`: `sourceDecls`.
- **Remove only if:** never.

### The library's initializers run at their module's place, always

- **What:** The startup walks the imports from `main`'s module with the
  toolchain's modules included, and runs every `initialize` declaration
  of each `Init` and `Std` module it reaches, used or not, at that
  module's place among the program's modules, each module's in source
  order, for its phases. In Lean 4.34.0 that is one initializer,
  `IO.stdGenRef`. A `prelude` program whose imports do not reach
  `Init.Data.Random` does not run it, and one that lists another module
  first runs that module's initializers first. In a program that uses the
  `Lean` package (a module of it in the walk), the initializers of all of
  `Init` and `Std` run before anything else, as `lean_initialize()` runs
  them (lean2rr loads the modules `Init` and `Std` when the imports do not
  reach them); then the `Lean` package's `initialize` constants that the
  program uses, by module and position. Every other toolchain constant is
  evaluated lazily, once, and only those the program uses are translated.
  With the optimization `unread-fields` (off by default), "uses" means
  that code the pass keeps reads the constant: the step of a `Lean`
  package's constant that only code it left out read does not run
  (`Main.pipeline`; [../optional-passes.md](../optional-passes.md#values-in-unread-fields-are-left-out-unread-fields)).
  The steps of `Init`, `Std` and the program always run.
- **Why:** Natively every initializer of a module that is initialized
  runs, at the module's place in the walk (`emitInitFn`). An initializer
  is an action whose effects show: `IO.stdGenRef` opens and reads
  `/dev/urandom`, and with no descriptor left (`ulimit -n 11`) the native
  program stops with `uncaught exception: resource exhausted (error code:
  24, too many open files)` / `  file: /dev/urandom`, exit 1. lean2rr ran
  it only for programs that used it, and so ran `main` (lean-runtime case
  io/startup_fd_limit; test `RtStartupInitUrandom`). Then it ran it before
  every program initializer, where a `prelude` program's module listed
  before `Init.Data.Random` initializes first (review RSG-01; test
  `RtStartupInitOrder`, with the companion module `StartupInitOrderDep`),
  and not at all in a `prelude` program that imports a `Lean` module but
  not `Init.Data.Random`, where `lean_initialize()` runs it (RSG-02; test
  `RtStartupInitLeanPkg`). Natively an error in `lean_initialize()` aborts
  the program (`libc++abi: terminating due to uncaught exception of type
  lean::exception: …`, status 134); lean2rr reports it as an uncaught
  exception, exit 1, as for any program (RSG-03; plan §10; the test's
  expectation files). `lean_initialize()` is modelled once for the whole
  program, not per module as natively, and a program that imports part of
  `Lean` loads `Init` and `Std` too (RSG2-01, RSG2-02: plan §10, known
  differences of programs that use the `Lean` package, which are not a
  target), each only if it can be loaded with the program: `Std`'s
  modules can declare a name the program declares (`ByteSlice`), which
  natively is no clash; without `Std` the startup is the same, as `Std`
  has no initializer (lean2rr prints a note; test `RtShimClashLean`). The library's other constants are pure: evaluating
  them on first use instead of at startup does not show. `IO.rand` reads
  the seeded generator from its once-cell and never seeds it again (test
  `RtStartupInitRand`). Cost: a few functions per program (the
  initializer, `IO.mkRef`, `mkStdGen`, `ByteArray.toUInt64LE!` and its
  panic message). The `Lean` package's thousands of `builtin_initialize`
  declarations are not run (plan §10).
- **Where:** `Emit/Startup.lean`: `startupItems`, `libraryModuleItems`,
  `usesLeanPackage`, `leanInitModules`, `initItem?`, `startupModules` and
  `importPostOrder` (`toolchain`); `Emit/Entry.lean`: `programRoots`,
  `startupSteps`; `Env.lean`: `loadEnvironment`; `CompileRecord.lean`:
  `isLibraryModule`, `isToolchainModule`; `Main.lean`: `pipeline` (with
  `unread-fields`, `isUsedInit`, the steps dropped); `Opt/UnreadFields.lean`:
  `markExtern`, `markRoot`.
- **Remove only if:** never. Check the list when the toolchain changes
  (an `[init]` or `[builtin_init]` attribute in `Init` or `Std`).

### The startup chain is cut into chunks of 128 steps

- **What:** The startup steps are emitted as functions of at most 128
  steps each (`l2r_init_chunk_N`), called in order, with a further level
  of grouping when there are more than 128 chunks; `l2r_init_body` runs
  them. An initializer's error is reported like an uncaught exception of
  `main` (exit 1), and later initializers do not run.
- **Why:** One chain of nested matches would be as deep as the program has
  initializers, and rrc's recursive lowering overflows its stack on a few
  thousand (5000 initializers; adv3 CN3-07, 96a1ef7).
- **Where:** `Emit/Startup.lean`: `startupChunk`, `startupChain`;
  required part `startup-chunks` in `Opt/Registry.lean`.
- **Remove only if:** rrc lowers deep nests without recursion.

### lean2rr never runs the program's initializers

- **What:** lean2rr loads extension states without Lean's init step.
- **Why/Where:** see
  [../translator.md](../translator.md#extension-states-are-loaded-without-running-initializers).
- **Remove only if:** never.
