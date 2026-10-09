# `lcAny`, relevance, and the "can cast" fact

Where a static type is unavailable, lean2rr uses the uniform `Box`
representation (see
[../representations/box-and-uniform.md](../representations/box-and-uniform.md)).
This file covers when a type counts as unknown, and the whole-program fact
that decides how much an unknown value may be read as. Paths are relative
to `lean2rr/LeanToReussir/`.

### Only `lcAny` in a relevant position is data of unknown type

- **What:** A parameter of an inductive is *relevant* when it occurs, in
  a relevant position, in some data field of a constructor (least
  fixpoint over the program's inductives). Stage 3 counts a binder's type
  as unknown only for an `lcAny` in a relevant position, and compares types
  with phantom arguments erased (`normTy`). `ST.Ref`, `Array`, `Thunk` and
  `Task` have fixed relevance (their payload is not a Lean field). Stage 4
  does not use relevance: a generated nominal type is one per inductive.
- **Why:** An `lcAny` in a phantom position (`EST.Out ε lcAny α`'s state)
  carries no data, so Stage 3 has nothing to recover there.
- **Where:** `Relevance.lean`: `computeRelevance`, `builtinRelevance`,
  `hasRelevantAny`; `MonoRetype.lean`: `programRelevance`, `isUnknown`,
  `normTy`.
- **Remove only if:** never.

### Type arguments that are not statically known become `lcAny`

- **What:** A type argument that mentions a variable (a type taken out of
  an existential package, a type Lean's specializer turned into a value)
  or that a partial application leaves open is `lcAny`: the call goes to
  the uniform instance. Nothing is rejected.
- **Why:** Lean itself treats every value uniformly, so `lcAny` is always
  correct, only slower. Such arguments used to be erased, which is wrong
  for relevant positions (adv round 1, 3f59239).
- **Where:** `Mono.lean`: `renameApp`, `normTypeArg`; plan
  [§2.3](../../translation-plan.md#23-instances),
  [§2.6](../../translation-plan.md#26-when-a-type-is-not-statically-known).
- **Remove only if:** never.

### Lean library code that relies on the uniform representation

- **What:** `NonScalar` and `PNonScalar` (types that stand for "any
  object") become `lcAny` in every type, and `NonScalar.mk`/
  `PNonScalar.mk` (used only to build Lean's `box(0)` placeholder) become
  `◾`. The `unsafeCast`s around them (erased by LCNF) become ordinary
  representation conversions: boxing or unboxing one element (an
  `Array α` and an `Array NonScalar` are one array of boxes).
- **Why:** `Array.mapMUnsafe` (behind `Array.map`) and `mapFinIdxMUnsafe`
  reinterpret an `Array α` as an `Array NonScalar` and replace elements one
  by one with values of another type; `Array.modifyMUnsafe` stores
  `unsafeCast ()` into the slot being updated so the element stays
  unshared. This code is inlined into user code's persisted LCNF, so it
  must be translated as it is (data holding cast values: F04GuardCast,
  354b5cc). Stage 3 then recovers the precise types around it
  ([type-recovery.md](type-recovery.md)), and placeholders become zeros
  ([../representations/placeholders.md](../representations/placeholders.md)).
- **Where:** `Mono.lean`: `isUniformConst`, `uniformTy`, `uniformCode`,
  `uniformDecl`; `MonoTypesKeep.lean`: `toMonoTypeKeep` (in mono types);
  plan
  [§2.7](../../translation-plan.md#27-library-code-that-relies-on-the-uniform-representation).
- **Remove only if:** Lean's library stops relying on the uniform object
  representation.

### Whether the program can cast at all is a whole-program fact

- **What:** `LowerCtx.programCasts` is true when some declaration the
  program reaches, outside Lean's library (`Init`, `Std`, `Lean`, `Lake`)
  and lean2rr's shim (`L2RShim`), is `unsafe` (whatever its name; the
  `_unsafe_rec` code Lean (4.33, 4.34) generates for a `partial def` is not
  `unsafe`, so `partial` alone does not count), is an axiom (not one of
  Lean's axioms of native evaluation, next entry), uses `sorry`,
  is `implemented_by` an `unsafe` function (even a library one), or is an
  `@[export]` definition under a C symbol of Lean's library or one that
  starts with `l2r_` (`librarySymbols`). An extern of the program does
  not count by itself: the walk goes into the code that runs for it
  ([../externs-ffi/program-externs.md](../externs-ffi/program-externs.md#an-extern-of-the-program-is-not-a-cast-by-itself)).
  The declarations reached are those the program's code comes from
  (`sourceDecls`) and, transitively: the constants their definitions
  mention; their `implemented_by` targets; their `_unsafe_rec` copies (the
  code Lean compiles for a recursive definition; for a `partial def`, whose
  value is only an inhabitant of its type, the only place its code shows);
  the `@[export]` definitions of an extern's C symbol. Every `@[csimp]`
  replacement that is a declaration of the program is also a root,
  whether or not the walk reaches the constant it replaces
  (`programCsimps`): compiled code calls the replacement and may
  inline it, and the replaced constant may show only in compiled code
  (a library `@[macro_inline]` definition such as `ite`, whose value the
  walk does not enter, becomes `Decidable.casesOn`). The replacements are
  those of `CSimp.ext`'s state after import and, for `local` and `scoped`
  ones, which that state lacks, the `g` of every constant of the
  program's modules stated as `@f = @g`. Every user reads the same fact,
  computed once (`lowerProgram`): the cast arms of the unboxing functions
  (`boxCastable`), `ErasedDomains` (`flowAnalysis`), the compact arrays
  (`compactArrayKinds`); `unread-fields` computes it on the code it keeps.
  Only then do `Box`
  unboxing functions accept the variants of *other* types that an
  `unsafeCast` can read; otherwise they match only the representations of
  their own Lean type.
- **Why:** Matching every type a cast could read made unboxing functions
  quadratic in the number of same-shape boxed types (round 6 TY6-02,
  5be764c). The individual conditions each come from a review finding:
  an extern's type is not compared with the `@[export]` definition
  lean2rr calls instead (RV6T-01: every extern and `@[export]` of the
  program counted; an extern of the program is now bound to an `@[export]`
  only when their types and compiled signatures agree, so RV6T-01's
  program is refused, test `RtCastExtern`; and it runs no C, so since
  2026-10-09 only an `@[export]` that lean2rr calls unchecked counts:
  every extern turned compact arrays and `unread-fields` off, lean-zip's
  among them, test `RtCArrExtern`); an unsafe declaration with any name
  can cast (RV6T-02); `@[implemented_by TypeName.mk]` gives two types one
  `TypeName`, so `Dynamic.get?` reads one as the other (RV6T-05). The
  walk missed a `partial def`'s code (its `_unsafe_rec` copy) and a
  `@[csimp]` replacement: a cast inlined there (through a safe declaration
  implemented by an `unsafe` one) left the program counted as one that
  cannot cast, and the program lean2rr built stopped at an unboxing with
  "INTERNAL PANIC: unreachable code has been reached" (tests
  `RtCastPartial`, `RtCastCsimp`, `RtCastExternBody`; for a `local` or
  `scoped` `@[csimp]`, review of that fix, `RtCastCsimpLocal`,
  `RtCastCsimpScoped`; for a replaced constant that only a library
  `@[macro_inline]` body mentions, `RtCastCsimpMacroInline`).
  Lean's own library casts only where lean2rr's representations agree.
- **Where:** `Lower/Conv.lean`: `programCasts`, `sourceDecls`,
  `librarySymbols`, `exportsBySymbol`, `programCsimps`,
  `boxCastable`; `LowerBase.lean`:
  `LowerCtx.programCasts`; `Emit/Program.lean`: `lowerProgram`
  (`L2R_DEBUG` prints the deciding declaration); plan [§5.1](../../translation-plan.md#51-type-translation).
- **Remove only if:** never. It relies on library modules being the
  toolchain's: a program module named `Init.*`, `Std.*`, `Lean.*` or
  `Lake.*`, or `L2RShim.*` (trusted too, `isToolchainModule`), that is not
  the toolchain's or the shim's is rejected at load (RV6T-06, RV8L-01; see
  [../translator.md](../translator.md#program-modules-named-like-leans-library-are-rejected)).
  How each cast converts: [../conversions/casts.md](../conversions/casts.md).

### Lean's axioms of native evaluation are no cast

- **What:** An axiom that Lean adds for a proof by native evaluation does
  not make the program cast, when the evaluation ran the code of the
  definitions. `native_decide`, `decide +native` and `bv_decide` call
  `Lean.Meta.nativeEqTrue` (Lean 4.34, `Lean/Meta/Native.lean`). It
  compiles a closed `Bool` term `e`, runs it, and adds an axiom only when
  the result is `true`. The axiom is `<decl>._native.<tactic>.ax_<i>… :
  e = true` (exactly `@Eq.{1} Bool e true`; under the module system the
  name has `_private.…` in front). `nativeEvalStatement?` accepts exactly
  that name and that statement. `nativeExempt` decides which of these
  axioms are exempt; the main walk of `programCasts` counts every other
  axiom, and goes on into the constants of `e` for an exempt one.
  - **The walk of an evaluation** (`nativeEvalWalk`): from the constants
    of `e` through the program's definitions and `_unsafe_rec` copies, not
    into Lean's library. From each constant `f` it reached, it also goes
    to `g` for every `@[csimp]` candidate `f ↦ g`, because compiled code
    runs `g`. The program's replacements of library constants are roots
    too. The axiom is not exempt when the walk meets an `implemented_by`
    target, an extern or an `initialize` constant of the program
    (`getInitFnNameFor?`), or kernel evaluation.
  - **The `@[csimp]` candidates** (`programCsimps`): every constant of a
    module of the program stated `@f = @g`. Every `@[csimp]` theorem is
    one, also a `local` one, which no file records, and one that another
    module makes a `local` `@[csimp]` theorem. A candidate is dangerous
    when its proof can be false (`proofAxioms`, like `#print axioms`
    through the program's declarations): it uses `sorryAx`, an axiom of
    the program that is not exempt, or kernel evaluation. A dangerous
    candidate acts on an axiom when the axiom's walk reached its `f`, or
    its `f` is a library constant. It does not act on an axiom that it
    comes after: the axiom is its own (the declaration in the axiom's name,
    `nativeAxiomDecl?`, is the candidate), or its proof uses the axiom.
    An axiom on which a dangerous candidate acts is not exempt.
  - **The fixed point:** a candidate proved with an axiom of native
    evaluation is dangerous until that axiom is exempt. `nativeExempt`
    starts with no axiom exempt, so every candidate whose proof uses an
    axiom is dangerous. Then it makes exempt each axiom that passes both
    tests, and computes the dangerous candidates again. It stops when the
    exempt set no longer grows. Axioms and candidates that only justify
    each other stay out.
  - **Kernel evaluation** (`isKernelEvalConst`): `Lean.reduceBool`,
    `Lean.reduceNat`, `Lean.ofReduceBool` and `Lean.ofReduceNat` count
    when the main walk reaches them, in a value or in the type of a
    declaration it reaches, before it skips the library. The kernel
    proves `reduceBool c = b` by running the compiled code of the
    constant `c`, which can be the program's.
  `L2R_DEBUG=1` prints `program casts: yes (<axiom>)` for an axiom that
  counts.
  Examples:
  - `theorem t (x : UInt64) : x &&& 7 < 8 := by bv_decide` adds
    `t._native.bv_decide.ax_1_5 : verifyBVExpr t._expr_def_1_1
    t._cert_def_1_1 = true` (the two definitions hold data of the
    library's types). It is no cast (test `RtCastNativeAxiom`, with
    `native_decide` too).
  - `theorem tableOk_eq : tableOk = true := by native_decide` is a
    candidate, but its axiom `tableOk_eq._native.native_decide.ax_1_1` is
    its own, so it acts on nothing; the axiom is exempt, and then the
    candidate is not dangerous (test `RtCastNativeEqIdiom`, with an
    equation lemma; `RtCastNativeLibShape`: `@List.length = @myLength`
    proved with standard axioms only).
  - `axiom bad : true = false` counts. It proves `False`, and so
    `Array UInt64 = Array Float` (test `RtCastAxiomBoolEq`).
  - `@[implemented_by lieImpl] def lie : Bool := false` with `lieImpl`
    giving `true`: `theorem lieTrue : lie = true := by native_decide`
    adds a false axiom, which counts (test `RtCastNativeImplBy`). So does
    `Lean.ofReduceBool lieAux true rfl` with `def lieAux := lie` (test
    `RtCastReduceBool`), and `congrArg Lean.reduceBool` without
    `ofReduceBool` (test `RtCastReduceBoolCongr`).
  - A candidate proved by `sorry` acts on a later axiom whose evaluation
    reaches its `f` (test `RtCastNativeCsimp`): also when the axiom is
    `f_eq.lie`'s and the candidate is `f_eq` (`RtCastNativePrefix`), when
    another module declares the candidate and this one makes it a `local`
    `@[csimp]` theorem (`RtCastNativeCrossLocal`), and when the candidate
    is named `d.eq_1` beside an `unsafe def d` (`RtCastNativeEqnName`).
- **Why:** An axiom `e = true` that is true of the definitions is a
  theorem: the program could prove it without the axiom (by `decide` or
  `rfl`, if slowly). So it proves no equation between two types that an
  axiom-free program could not prove. The evaluation is the evidence that
  it is true: Lean trusts its compiler for it (`Lean.trustCompiler`), and
  so does lean2rr. That evidence holds only for code that is the code of
  the definitions. An `implemented_by` target is checked against the
  declared type only, so a wrong one lets `native_decide` prove `False`
  (Lean's `implemented_by` doc says so), and an extern ran its C natively.
  A `@[csimp]` theorem can make compiled code compute another value only
  when the theorem is false, and a false theorem needs an axiom that can
  be false in its proof. So a candidate whose proof uses only Lean's
  standard axioms (`propext`, `Quot.sound`, `Classical.choice`) is
  ignored, wherever and however it is declared. A partial or `opaque`
  definition without `implemented_by` does not count: its code is the same
  in every build, so every axiom about its value agrees with every other,
  and the kernel cannot unfold it to contradict them. A constant that an
  `initialize` (or `builtin_initialize`) action sets is not so: the action
  runs when a module imports it, so its value can differ between the
  builds of two modules. With an environment variable set for one build
  and not for the other, `(flag && true) = true` and `(flag || false) =
  false` were both exempt and proved `False` (review of 7732aaef; test
  `RtCastNativeInit` checks one such axiom). Earlier
  versions of this rule scoped the candidates by module, import and name,
  and each scope had a hole (reviews of 32c81df1 and 55514050): counting
  every `@f = @g` statement made the usual `native_decide` idiom a cast;
  a name-prefix test, a module scope for `local` attributes and an
  exception for equation lemmas by name let a false axiom pass, and the
  program lean2rr built stopped at an unboxing with "INTERNAL PANIC:
  unreachable code has been reached". So did kernel evaluation, which the
  walk skipped as library code (also on dev before). Before 2026-10-09 the
  compact arrays let every axiom that states a `Bool` equation pass
  (`isBoolEqAxiom`), a user's false one too, and the other users of the
  fact let no axiom pass: lean-zip's `bv_decide` axioms kept
  `unread-fields` off and gave its unboxing functions their cast arms.
- **Where:** `Lower/Conv.lean`: `nativeEvalStatement?`, `nativeExempt`,
  `nativeEvalWalk`, `proofAxioms`, `nativeAxiomDecl?`, `isKernelEvalConst`,
  `programCsimps`, `programCasts`.
- **Remove only if:** never while axioms can be cast sources. The name
  test assumes that only Lean names an axiom `…._native.<tactic>.ax_<i>`.
  Lean accepts that name from the user, so a user axiom with that name and
  that statement shape passes: `axiom foo._native.native_decide.ax_1 :
  (!true) = true` proves `False`, and the program lean2rr builds stops at
  an unboxing (`false = true` too). Lean's library is trusted: its own
  `@[csimp]` theorems, `implemented_by` targets and theorems are taken as
  true. A Lean compiler bug that makes the evaluation wrong is not
  detected either (plan §10 has one: an erased join-point parameter; with
  `native_decide` it proves `False`).
