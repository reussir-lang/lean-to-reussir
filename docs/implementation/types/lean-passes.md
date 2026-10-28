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
  function. `toMonoK` also binds the field of a `cases` on an `Array`, a
  `ByteArray` or a `FloatArray` at the field's own type (`List α`,
  `Array UInt8`, `Array Float`), where Lean's binds it at `lcAny`
  ([../representations/compact-arrays.md](../representations/compact-arrays.md#a-match-on-an-array-takes-the-array-at-its-own-type)).
- **Why:** Lean erases every type-former argument: `Std.HashMap Nat Nat`
  is `DHashMap Nat (fun _ => Nat)`, whose buckets became
  `AssocList Nat lcAny`, so every value was boxed (hashmap: 2.7x → 1.24x
  native memory, 1.86x → ~1.3x time, 982fc77). Both passes compute types,
  so both must use the same conversion.
- **Where:** `MonoTypesKeep.lean`: `toMonoTypeKeep`, `keepFormer?`;
  `TypedToMono.lean` (`toMonoK`; `casesArrayToMonoK`,
  `casesByteArrayToMonoK`, `casesFloatArrayToMonoK`); `TypedStructProjCases.lean`
  (`structProjCasesK`); `Opt/Registry.lean`: `stage2`.
- **Remove only if:** Lean's own `toMonoType` keeps such arguments. The
  rule is syntactic, after eta reduction: `fun n => Fin n` is `Fin`, kept;
  `fun n => Fin (n + 1)` is kept too, since Lean's base code already
  writes `Fin (n + 1)` as `Fin lcAny`; `fun b => cond b Nat String` stays
  `lcAny` (plan
  [§3](../../translation-plan.md#3-stage-2--leans-mono-pipeline-leans-passes-driven-by-us),
  corrected by 4ad6df7).

### Closed terms are extracted last, as Lean ran it

- **What:** `extractClosed` is taken out of the pass list and run after
  every other pass, over all declarations, module by module in Lean's
  order with one cache per module: first the declarations whose extraction
  made closed terms (`d._closed_N` in the module's IR-only declarations),
  in the order Lean made them, then those whose IR reads a closed term;
  the others are left as they are. Afterwards the dead reads of closed
  terms are dropped and dead calls kept, as Lean's impure `elimDeadVars`
  does. lean2rr's copy of the pass looks up attributes and kernel types on
  the declaration of Lean's compilation an instance comes from, and
  recognizes an array literal (`searchArrayLiteral`: `Array.mkEmpty` or
  `Array.emptyWithCapacity`, then `Array.push` per element) by those
  declarations too (`leanCall?`): a literal of Stage 1's instances
  `Array.push._l2r.k` is one closed term, as natively (before 2026-10-28,
  one closed term per element, a chain).
- **Why:** With one cache for the whole program, another declaration
  owned shared terms (the evaluation order inside constants differed), the
  calls Lean leaves dead after a cache hit were missing, and
  `set_option compiler.extract_closed false` was ignored (6727721). An
  instance `f._l2r.k` is not a kernel constant, so `@[never_extract]` and
  Lean's "callee has a function type" check (`def F := Nat → Nat`) would
  not see it.
- **Where:** `Pipeline.lean`: `extractLikeLean`, `leanNameOf`;
  `ExtractClosedK.lean` (`leanName`, `leanCall?`, `searchArrayLiteral`),
  `Decl.elimDeadLikeImpure`,
  `safeToElim`; `CompileRecord.lean`: `closedRecord`, `closedTermOwner?`,
  `moduleIRDeclsImpl`.
- **Remove only if:** never: which declaration evaluates a shared closed
  term, and when, is observable through traces and panics.

### A closed term is shared between instances with the same mono images

- **What:** A term that misses Lean's cache is looked up, and then cached,
  under a second key too (`closedMonoKey`, one cache per module like
  Lean's): its code as an expression with each instance `f._l2r.k` (and
  its `_redArg`) replaced by `f` (or `f._redArg`), the mono images of its
  type arguments (`toMonoTypeKeep`) and its static dictionaries. The key
  is used only when no image has an `lcAny` that its type argument has
  not (a type argument that is `lcAny` itself, hidden or uniform, is the
  same in both instances) and the term's type serves at itself
  (`Mono.serves`: it mentions no `lcAny`), and only in a declaration made
  from an instance without type arguments, or at `lcAny` for each
  (`monoOwner`: a monomorphic declaration or a specialization Lean made,
  whose code is concrete natively too); other declarations made from an
  instance (`_lam_N`, `_closed_N`) are compared by name.
  Example: `@[noinline] def mk {α} (n : Nat) : Option α` called as `mk 5`
  in four declarations at `Option (Fin 3)`, `Option (Fin 5)`,
  `Option Nat` and `Option W` (`structure W where x : Nat`): Stage 1 makes
  instances at `Fin 3` (also serving `Fin 5`), `Nat` and `W`, one closed
  term now, three before.
- **Why:** Natively `mk` is one function, and Lean's cache compares mono
  terms, in which type arguments are erased and types are mono types: the
  four calls are one term, `mk ◾ 5 : Option Nat`, so a trace in `mk`
  printed three times where natively once (a bug hunt of the extern
  routing, 2026-10-27, test `RtClosedMonoEqual`). Instances whose type
  arguments have equal images run the same mono code. An `lcAny` that the
  image introduced (an instance at a type former such as `fun α => Nat →
  α × Nat` has the image `lcAny`) does not tell that code apart, and an
  `lcAny` in the term's type can hide a type argument; the numbering of
  `_lam_N` and `_closed_N` follows the extraction's order, not only the
  instance. An instance of a generic declaration has concrete types where
  native Lean's generic code has `lcAny`: `mk2 7` in `gen {α}` is natively
  a term at `Option lcAny`, which Lean's cache does not share with
  `user`'s `mk2 7 : Option Nat`; without `monoOwner`, `gen` at `W` read
  `user`'s term, one trace for native two (review of the bug hunt, repro
  V3b, in `RtClosedMonoEqual`). Those terms stay apart, natively one
  (plan §10, "Merging after erasure"), as do terms at type arguments that
  only Lean's `toMonoType` makes equal. Lean's own cache still shares an
  instance's term with a concrete declaration's when both call the same
  instance (`gen` at `Nat` and `user`: one trace, natively two; plan §10,
  kept as it is).
- **Where:** `Pipeline.lean`: `closedMonoKey`, `closedInstMarker`,
  `monoOwner`, `extractLikeLean`; `ExtractClosedK.lean`: `monoKey`,
  `monoCache`, `performExtraction`; plan
  [§3](../../translation-plan.md#3-stage-2--leans-mono-pipeline-leans-passes-driven-by-us).
- **Remove only if:** Stage 1 stops making an instance per type.

### Join-point parameters are put in the order of their first use

- **What:** After every pass of Stage 2 (`extractClosed` included), the
  parameters of each join point are put in the order of their first use
  in its body. The parameters that the body does not use come last, in
  their old order. Known gap: that old order is Lean's hash order, so two
  or more unused parameters (Lean runs no `reduceJpArity` after
  `extendJoinPointContext`, and `elimDeadBranches` can make a use
  unreachable) can still change order when an unrelated definition is
  added; this is rare and does not change results. Each jump passes its arguments in the new order. Inner
  join points are put in order first, so the order of an outer one
  follows the code after that change. A join point whose type depends on
  one of its parameters keeps its order (mono code has none).

  ```
  jp _jp.1 (x.7 : Nat) (y.3 : Nat) : Nat :=      -- before (hash order)
    let z := Nat.add y.3 x.7 ...
  jp _jp.1 (y.3 : Nat) (x.7 : Nat) : Nat :=      -- after (first use)
    let z := Nat.add y.3 x.7 ...
  ```
- **Why:** Lean's `extendJoinPointContext` adds the variables that a join
  point uses as new parameters in the order of a hash map over their
  unique ids. One counter draws these ids for the whole program in Stage
  2's session, so a definition added anywhere changed the order of
  parameters in code that it does not touch: a J2 join point's tuple
  type, an outlined join point's parameters, a state machine's slots.
  The determinism check found this (`determinism-check.sh`:
  RtTaskConvSync, RtSmDecode, RtStateMachines, RtJpSlots). Results were
  not affected.
- **Where:** `Pipeline.lean`: `stableJpParams` (called by `runStage2`),
  `stableJpParamsCode`, `jpParamOrder?`, `firstUses`, `permuteDomains`.
- **Remove only if:** Lean's `extendJoinPointContext` gives an order that
  does not depend on the unique ids (the determinism check of the
  programs above then passes without it).

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
