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
  `unsafe`, so `partial` alone does not count), is an axiom, uses `sorry`,
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
  (`programCsimpTargets`): compiled code calls the replacement and may
  inline it, and the replaced constant may show only in compiled code
  (a library `@[macro_inline]` definition such as `ite`, whose value the
  walk does not enter, becomes `Decidable.casesOn`). The replacements are
  those of `CSimp.ext`'s state after import and, for `local` and `scoped`
  ones, which that state lacks, the `g` of every constant of the
  program's modules stated as `@f = @g`. Only then do `Box`
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
  `librarySymbols`, `exportsBySymbol`, `programCsimpTargets`,
  `boxCastable`; `LowerBase.lean`:
  `LowerCtx.programCasts`; `Emit/Program.lean`: `lowerProgram`
  (`L2R_DEBUG` prints the deciding declaration); plan [§5.1](../../translation-plan.md#51-type-translation).
- **Remove only if:** never. It relies on library modules being the
  toolchain's: a program module named `Init.*`, `Std.*`, `Lean.*` or
  `Lake.*`, or `L2RShim.*` (trusted too, `isToolchainModule`), that is not
  the toolchain's or the shim's is rejected at load (RV6T-06, RV8L-01; see
  [../translator.md](../translator.md#program-modules-named-like-leans-library-are-rejected)).
  How each cast converts: [../conversions/casts.md](../conversions/casts.md).
