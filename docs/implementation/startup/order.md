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
  "Not supported"). Two exceptions: with the optimization `unread-consts`
  (on by default), an unread constant whose evaluation cannot show is not
  evaluated and not translated (below); with the optimization
  `unread-fields` (off by default), a constant's closed terms that only
  feed fields no kept code reads are not evaluated (the constant itself
  still is), so a `panic!` or `dbg_trace` in them does not show
  ([../optional-passes.md](../optional-passes.md#values-in-unread-fields-are-left-out-unread-fields)).
- **Where:** `Emit/Startup.lean`: `startupItems`, `StartupItem`;
  `Emit/Entry.lean`: `entryRoots`, `programRoots`.
- **Remove only if:** never.

### An unread constant whose evaluation cannot show is left out (`unread-consts`)

- **What:** After Stage 1, the startup step of a constant goes when both
  hold:
  - *unread*: the code that `main`, the error printer and the other
    startup steps reach (calls, closures, constant reads, transitively)
    does not name the constant's instance;
  - *quiet*: its evaluation cannot show. The constant's code and the code
    of every instance it runs (a call with all its parameters, a constant
    read) only bind literals, build constructors and closures, project
    fields, match, jump and return, and call the externs in
    `pureExterns` (total arithmetic and conversions of `Nat`, `Int`, the
    fixed-width numbers and floats; array and string operations whose
    index has a proof; never `panic`, `dbg_trace`, IO, tasks, thunks,
    references, `!` reads, `sorryAx`). No function value is applied (a
    closure is only built). A recursion among these instances counts
    only when every instance on it comes from a definition of Lean's
    toolchain that Lean checked (structural or well-founded recursion),
    or from an `unsafe` implementation of one (the loop of
    `Array.foldlMUnsafe`); never a `partial` definition, never the
    program's own recursion. The program's own `unsafe` code keeps the
    constant, except Lean's computed-field implementations
    (`BVExpr.const._override`; `isComputedFieldImpl`: `p._override`, the
    `implemented_by` of `p`, where `p` is a constructor or the `casesOn`
    of a type with computed fields, `computedImpl?`, or a function tagged
    `@[computed_field]`, which Lean allows only in an inductive's `with`
    block; the name alone counted before, so a program's own
    `unsafe def stepI._override` passed, test
    `RtNameOverrideUnreadConst`). A constant whose type mentions a task,
    thunk, reference or promise stays (the persistence walk at its first
    evaluation, constants.md). An instance whose declaration rests on a
    claim that Lean did not check keeps the constant (`axiomTaints`):
    - an axiom other than `propext`, `Quot.sound` and
      `Classical.choice`: `sorryAx`, a user `axiom`, and the axiom that
      `native_decide` adds in Lean 4.34 for each use
      (`t._native.native_decide.ax_1_1`; sound when the compiler is, so
      this is conservative);
    - an `@[implemented_by]` of the program: the target can compute other
      values than the declaration, with no axiom at all (`stepI 0 = 1`,
      its target gives 0: a range's `step_pos` is about the declaration,
      the loop runs the target). Lean's computed-field implementations
      (`isComputedFieldImpl`) do not count.
    As Lean's `collectAxioms`, the walk goes through the types and values
    of the declarations, transitively, and through an inductive type's
    constructors. It also goes where the compiled code is not the
    kernel's term: into the `implemented_by` target; into `f._unsafe_rec`
    for a `partial` definition `f` (the code that runs; the kernel's `f`
    is an opaque constant); and, for a reference to `f`, into each
    theorem of the program stated as `@f = @g` and into `g`
    (`programCsimps`: every `@[csimp]` theorem, also a `local` or
    `scoped` one; the compiler runs `g` for `f`, and a theorem proved
    with `sorry` lets `g` compute other values). It stops at a
    declaration of Lean's toolchain that is not an axiom, but for
    `Lean.reduceBool` and `Lean.reduceNat` (the kernel reduces them by
    running compiled code; their values name `Lean.trustCompiler`): in
    Lean 4.34.0's `Init` and `Std` the only other axioms a declaration
    names are `lcProof` (in `unsafe` implementations) and
    `Lean.trustCompiler` (in those two). The toolchain's own
    `implemented_by`s and `csimp` theorems are trusted. One walk serves
    all constants: each declaration is visited once.
  Then the instances that only such constants reach go too (Stage 2 and
  later never see them), but not the `IO.Error` builders Stage 1 made
  (the lowering calls them by name for every fallible IO extern and
  child-process extern, also when only a left-out constant names one,
  `IO.Error.mkAlreadyExistsFile`: review of size-core, test
  `RtUnreadConstsIoErr`, and also when nothing names one). As a net, an
  instance that nothing reaches stays too: Stage 1 makes an instance
  without a reference in code only for these builders and for init
  functions, and an init function is a root through its `.init` step. A
  constant that kept code reads stays a startup step at its place: its
  evaluation, and the order, are as before. With `L2R_DEBUG` set, lean2rr
  prints the decision for every constant (`lean2rr: unread-consts: C:
  left out`, `…: kept, read`, `…: kept, <the reason>`).
- **Why:** Most unread constants are data that nothing reads: derived
  instances, parser descriptors of `syntax` commands, and the LRAT
  certificates (`*_cert__def*`, string literals up to 1.7 MB) and
  expression trees (`*_expr__def*`) that `bv_decide` stores as constants.
  The size survey of 2026-10-10 found them 23 % of the `.rr` text of the
  benchmark set and 50 % of a program that uses lean-zip. A constant of
  one string literal (the certificates) already has no function and no
  step (`literal-consts`, [constants.md](constants.md#a-constant-of-one-string-literal-is-read-from-the-literal-cache));
  this rule takes the rest: of the 50 distinct files of the benchmark set
  24.9 MB to 22.9 MB (−7.9 %), lean-zip's 4.3 MB to 3.6 MB (−16 %, its
  expression trees), lean-regex −12 %, cedar −6 %; rrc's build time grows
  with the code.
  Natively such a constant is evaluated once, at startup, and its value
  is never read. Its evaluation ends (no recursion but Lean's checked
  library recursion) and writes nothing (no extern but pure ones), so
  leaving it out changes no output, no exit code and no order of the other
  steps (the kept constants a dropped one reads are kept by others or are
  quiet too). Both "ends" and "never runs `unreach`" hold only when the
  proofs are true and the compiled code computes what the kernel's terms
  say. A false proof (made with `sorry` or a user axiom) can reach an
  `unreach` (`False.elim`: natively `INTERNAL PANIC: unreachable code has
  been reached` at startup) or make Lean's library recursion run for ever
  (`for i in r` over a `Std.Legacy.Range` of step 0 whose `step_pos` is
  `sorry`). So can compiled code that differs from the kernel's terms: a
  `@[csimp]` theorem proved with `sorry` or an `@[implemented_by]` that
  makes the step 0 at run time while `step_pos` is a true proof about the
  declaration, or `sorry` only in a `partial` definition's code. The pass
  left out all of these, and the program ran where native panics or
  never ends (hunt r7 B, and the review of its fix). The walk keeps
  them. What can differ is resource exhaustion: an evaluation that
  natively runs out of memory or stack, exceeds a size limit of Lean's
  runtime (`Nat.pow` of an exponent above 2^32) or runs for a very long
  time stops (or delays) the native program at startup, and lean2rr's
  program runs (plan
  [§10](../../translation-plan.md#10-known-divergences-and-unsupported-features),
  "Unread constants are not evaluated"). Memory and startup time drop.
  The interactions: the startup order of the steps that stay is
  unchanged (a filter); `boxed-consts`, `cheap-consts`, closed terms and
  once-cells, `unread-fields`, `conv-liveness` and `prelude-liveness` see
  fewer declarations and work as before on the rest; closed terms that
  Lean shared between a dropped constant and kept code are made again by
  the kept code (`ExtractClosedK` runs per module on what is left), which
  changes sharing only.
- **Where:** `Opt/UnreadConsts.lean`: `prune`, `blockers`, `scanCode`,
  `classifyCall`, `recursionEnds`, `isComputedFieldImpl`,
  `axiomTaints`, `standardAxioms`, `isAxiomLeaf`;
  `PureExterns.lean`: `pureExterns` (with `fixedWidthOps`, `floatOps`;
  also read by `Mono.erasedMerges`);
  `CompileRecord.lean`: `programCsimps`;
  hook `PassConfig.startupPrune`; `Main.lean`: `pipeline` (after Stage 1).
  Tests `RtUnreadConsts` (its `.l2r-debug` lists the decisions),
  `RtUnreadConstsIoErr`, `RtUnreadConstsSorry` (native panics at
  startup), `RtUnreadConstsAxioms` (`.l2r-debug`: `sorry`, a user axiom,
  `native_decide`, a `partial` definition, a `@[csimp]` theorem and a
  `local` one, an `implemented_by`, only standard axioms).
- **Remove only if:** the pass is off (every constant is a step).

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
