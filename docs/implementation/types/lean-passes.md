# Stage 2: Lean's mono pipeline, edited

Stage 2 runs Lean's own passes from `saveBase` to `saveMono` on the
monomorphic program, taken from Lean's pass manager, with the edits listed
in `Opt/Registry.lean` (`stage2`, printed by `lean2rr --list-opts`). Plan
[§3](../../translation-plan.md#3-stage-2--leans-mono-pipeline-leans-passes-driven-by-us).
Paths are relative to `lean2rr/LeanToReussir/`.

### `toMono` and `structProjCases` keep constant type families

- **What:** Lean's `toMono` and `structProjCases` are replaced by copies
  (`toMonoK`, `structProjCasesK`) whose type conversion, `toMonoTypeKeep`,
  keeps a closed, non-dependent type-former argument: a constant family
  `fun _ => T`, or a type constructor such as `List`. A family whose body,
  after eta reduction, mentions its variable stays `lcAny`. Every mono type
  lean2rr computes itself (constructor fields, Stage 3) uses the same
  function.
- **Why:** Lean erases every type-former argument: `Std.HashMap Nat Nat`
  is `DHashMap Nat (fun _ => Nat)`, whose buckets became
  `AssocList Nat lcAny`, so every value was boxed (hashmap: 2.7x → 1.24x
  native memory, 1.86x → ~1.3x time, 982fc77). Both passes compute types,
  so both must use the same conversion.
- **Where:** `MonoTypesKeep.lean`: `toMonoTypeKeep`, `keepFormer?`;
  `TypedToMono.lean` (`toMonoK`); `TypedStructProjCases.lean`
  (`structProjCasesK`); `Opt/Registry.lean`: `stage2`.
- **Remove only if:** Lean's own `toMonoType` keeps such arguments. The
  rule is syntactic, after eta reduction: `fun n => Fin n` is `Fin`, kept;
  `fun n => Fin (n + 1)` stays `lcAny` although every value is a `Nat`.
  (Plan §3 and the comment in `MonoTypesKeep.lean` still say
  `fun n => Fin n` stays `lcAny`; branch `fix-r7-front` corrects the
  plan.)

### Closed terms are extracted last, as Lean ran it

- **What:** `extractClosed` is taken out of the pass list and run after
  every other pass, over all declarations, module by module in Lean's
  order with one cache per module: first the declarations whose extraction
  made closed terms (`d._closed_N` in the module's IR-only declarations),
  in the order Lean made them, then those whose IR reads a closed term;
  the others are left as they are. Afterwards the dead reads of closed
  terms are dropped and dead calls kept, as Lean's impure `elimDeadVars`
  does. lean2rr's copy of the pass looks up attributes and kernel types on
  the declaration of Lean's compilation an instance comes from.
- **Why:** With one cache for the whole program, another declaration
  owned shared terms (the evaluation order inside constants differed), the
  calls Lean leaves dead after a cache hit were missing, and
  `set_option compiler.extract_closed false` was ignored (6727721). An
  instance `f._l2r.k` is not a kernel constant, so `@[never_extract]` and
  Lean's "callee has a function type" check (`def F := Nat → Nat`) would
  not see it.
- **Where:** `Pipeline.lean`: `extractLikeLean`, `leanNameOf`;
  `ExtractClosedK.lean` (`leanName`), `Decl.elimDeadLikeImpure`,
  `safeToElim`; `CompileRecord.lean`: `closedRecord`, `closedTermOwner?`,
  `moduleIRDeclsImpl`.
- **Remove only if:** never: which declaration evaluates a shared closed
  term, and when, is observable through traces and panics.

### `inferVisibility` and everything from `toImpure` on are not run

- **What:** Stage 2 stops at mono (plus `extractClosed`).
  `inferVisibility` is skipped too.
- **Why:** Boxing, reference counting and reset/reuse belong to Reussir;
  `inferVisibility` is module bookkeeping that transforms no code.
- **Where:** `Opt/Registry.lean`: `stage2`; `Pipeline.lean`:
  `stage2Passes`.
- **Remove only if:** never. (Lower/Borrow runs `toImpure` and the impure
  passes on *copies*, only to read Lean's borrow inference: see
  [../ownership.md](../ownership.md#borrowed-parameters-are-emulated-for-resources).)

### Groups bottom-up, checked after every pass

- **What:** Strongly connected groups of instances go callees first; the
  groups are split again after lambda lifting; Lean's LCNF checker runs
  after every pass (`--no-check` turns it off).
- **Why:** As `PassManager.run`: each pass can inline callees already
  processed; the checker catches a type error at the pass that made it.
- **Where:** `Pipeline.lean`: `runStage2`, `sccsBottomUp`;
  `Passes.lean`: `runPasses`.
- **Remove only if:** never.

### Extension states are loaded

- **What:** lean2rr imports the program with every extension's imported
  state, without running `[init]` declarations.
- **Why:** Without them, queries Lean's passes rely on (`isClass` for
  dictionary folding) silently answer `false`. See
  [../translator.md](../translator.md#extension-states-are-loaded-without-running-initializers).
- **Where:** `Env.lean`: `loadExtensionStates`.
- **Remove only if:** never.
