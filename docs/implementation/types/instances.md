# Stage 1: instances

Paths are relative to `lean2rr/LeanToReussir/` unless they say otherwise.

### Instances keep Lean's arity (Stage 1)

- **What:** In Stage 1, an instance keeps every type parameter of its
  declaration as an erased parameter, and its callers keep passing `◾`
  there. A partial application that stops before a type parameter calls
  the instance at `lcAny` for it; the parameter stays a parameter. Stages
  2 and 3 (Lean's passes, closed terms, startup constants) see these
  arities. Stage 4 then removes the erased parameters (rule 4: a function
  keeps one unit parameter for its trailing erased ones, see
  [../control-flow/calls-and-lets.md](../control-flow/calls-and-lets.md#erased-parameters-are-removed-rule-4)).
- **Why:** Arity decides when work runs (plan
  [§5.2](../../translation-plan.md#52-declarations-calls-arities)).
  Dropping type parameters in Stage 1 turned a function with only type
  parameters into a zero-parameter constant, evaluated once at startup
  where Lean runs it at every use (review finding fixed in 4674426); Lean's
  passes (`reduceArity`, `extractClosed`, `elimDeadBranches`) and lean2rr's
  own constant tests (`chainConsts`, startup `.caf` items, `safeToElim`)
  decide on these arities.
- **Where:** `Mono.lean`: `instantiate`, `renameApp`; plan
  [§2.3](../../translation-plan.md#23-instances).
- **Remove only if:** never; it is semantics.

### Instances get fresh names

- **What:** The instance `k` of declaration `d` is named `d._l2r.k`
  (`l_d___l2r_k_` once mangled). Uniqueness comes from the counter, not
  from an encoding of the type arguments.
- **Why:** Stage 2 runs Lean's passes, which inline by name. A fresh name
  guarantees they only ever see lean2rr's monomorphic copies, never Lean's
  saved polymorphic bodies.
- **Where:** `Mono.lean`: `freshInstName`, `instanceName`;
  `LowerBase.lean`: `fnName`; plan
  [§2.3](../../translation-plan.md#23-instances),
  [§5.13](../../translation-plan.md#513-names).
- **Remove only if:** never.

### Calls that Lean's CSE merges across types call one instance

- **What:** In each instance, after Stage 1's `simp`, the calls of a
  definition that Lean's mono-phase `cse` would merge into an earlier call
  of the same definition at other type arguments (a *group*) get one
  instance and the same arguments, and their binders the type of the new
  call. The grouping copies `Code.cse` on mono values: type arguments
  erased, merged variables identified, a trivial structure (`Subtype`,
  `Fin`, `Char`) taken for its field and `Decidable` for `Bool`; one scope
  per `cases` alternative, join points in the enclosing scope, a local
  function's body in its own (Lean's `cse` runs after lambda lifting);
  `@[never_extract]` calls apart. Constructors, extern instances and
  instances (dictionary builders) are not aligned. The instance of a group:
  1. The earlier call's, when its result serves every later call's
     (`serves`): the later calls get its type and value arguments and
     universe levels. Example: `gp xs none` as an `Option String`, then as
     an `Option (Nat → Nat)`: the value is `none` at both.
  2. Else the instance at `lcAny` for each type argument that differs, for
     every call of the group, the earlier one too (`uniformArgs`), with the
     earlier call's value arguments and universe levels. Example: `mkO n :
     Option (α → α)` at `Nat` and at `String` both call `mkO@lcAny`, whose
     `id` is a `Box → Box` closure; each use reads it at its own type
     through a wrapper. Each value argument that replaces another variable
     (merged into it) must serve at that variable's type, unless both are
     calls of one group that took the instance at `lcAny` (groups are
     decided in program order). A type argument that differs and is not a
     type (a type former: the callee's parameter has a kind that is not a
     sort) prevents this. So does a *closed* group (the earlier call uses
     only literals and other closed `let`s), unless the earlier call keeps
     its instance (every changed type argument is hidden, next entry) or
     the base test aligned every later call: `serves` with
     `strict := false`, the test before the review of the dependent-type
     work (`lcAny` hides nothing: equal types serve, `lcAny` and a type
     that holds only data serve, function types serve only when equal).
  3. Else only the later calls of 1 are aligned; the others run apart.

  `serves a b` walks the two types in parallel, as `toMono` sees them
  (`monoHead` at every level: a trivial structure is its field's type,
  `Decidable` is `Bool`, `NonScalar` is `lcAny`):
  - equal types serve, unless they mention `lcAny`;
  - an erased type serves; `lcAny` against another type does not;
  - two function types serve when their domains are equal and do not
    mention `lcAny`, and their codomains serve as codomains;
  - a function type and an inductive type, or two different inductive
    types, serve (no value has both types), but not as codomains;
  - two instantiations of one inductive serve when only parameters differ,
    no differing parameter is a type former or shows in no field, the type
    is not `Task`, `Thunk`, `ST.Ref` or `IO.Promise`, and the fields serve
    (instantiated, with a visited set);
  - anything else (`Quot`, an opaque type) does not.

  Nothing changes in an instance without a group.
- **Why:** Natively the calls are one after erasure and run once; two
  instances ran twice, so a panic or trace in them printed twice (cross-test
  XT-6, fixture A482; the dictionary and `Subtype` shapes: review XT6-02).
  With one layout per datatype (rule 1), two instantiations of one
  inductive (or of `Array`, `Thunk`, `Task`, `ST.Ref`, `IO.Promise`) are
  one Reussir value, so data needs no conversion. But an instance at
  concrete types reads its inputs at those types: `fst@Nat` unboxes a list
  element as a `Nat`, and a `Nat → Nat` closure has no conversion to
  `String → String`. A value made by the earlier call's instance and used
  at the later call's type takes inputs of that type only through its
  function values, so `serves` asks for the same domains there (review
  XT6-01: an unreachable panic; XT6-03: the same through a structure field;
  XT6-04: through a one-field structure, which mono identifies with its
  field). An `lcAny` can hide the type argument (`if b then List α else
  Unit` is `lcAny`): two equal types that mention it do not serve (review
  of the dependent-type work, shared case A833: `fst` passed as a value at
  `Nat` and at `String`, both `Bool → lcAny → Nat`, read a `String` element
  as a `Nat`). A closure is converted when it is used, so its results need
  a conversion even where no result can exist: hence the stricter
  codomains. The instance at `lcAny` is the uniform code that native Lean
  runs: its closures take boxes, so they serve both uses through boxes and
  wrappers; the earlier call's value arguments go into it, and it can
  return them, so they must serve at the types they replace; a call of a
  group at `lcAny` is the uniform value, which serves at every type of its
  group (`keep n (tagger n)` at `Nat` and at `String`). Aligning to the
  earlier call where possible keeps its type, as the merged variable has
  natively, so Lean's closed-term cache, which compares values and types,
  shares terms with other declarations as natively. The instance at
  `lcAny` is a closed term of its own: for `mkO 3` in one function at
  `Nat`, in another at `String` and in a third at both, it made three
  traces where native Lean and the base make two (review of this rule).
  So a closed group takes it only where the base merged the calls too
  (into the earlier call's instance, which was unsafe in the A833 class)
  or where the earlier call's instance does not change; otherwise it runs
  apart, as on the base. A wrong alignment crashes, a missed one only runs
  a call twice (plan §10), so anything unclassified refuses.
- **Where:** `Mono.lean`: `monoHead`, `mentionsAny`, `serves`,
  `uniformArgs`, `erasedMerges` (`L2R_DEBUG` prints each group's choice),
  `alignErasedMerges`, `monoInstance`; plan
  [§2.3](../../translation-plan.md#23-instances), §10 "Merging after
  erasure"; tests `RtCseAcrossTypes`, `RtCseFnValues`, `RtCseResidual`,
  `RtCseFnField`, `RtCseFnTrivial`, `RtCseFnResult`, `RtCseHiddenAny`,
  `RtCseUniform`, `RtCseClosed`, `RtCseApart` (expectation files: the
  shapes that still run apart or more often than natively), `RtDepXA833`,
  `RtDepXD71TesterT23`.
- **Remove only if:** Stage 1 stops making an instance per type, or Lean's
  `cse` starts comparing type arguments.

### A type parameter that shows nowhere in the declaration's type gets `lcAny`

- **What:** At a call of a definition (not an extern), a type argument
  whose parameter is a type (its kind is a sort) and shows in no later
  parameter's type and not in the result type, in the callee's LCNF type
  (`typeParamHidden`), is replaced by `lcAny` in the instance key
  (`renameApp`): every call, at every type, calls the instance at `lcAny`.
  Example: `len {α} (b : Bool) (v : if b then List α else Unit) : Nat` has
  the type `Bool → lcAny → Nat` at every `α`; a phantom parameter
  (`ph {α} (n : Nat) : Nat`) too.
- **Why:** The instances would all have the same type, and natively the
  function is one: Lean's closed-term cache, which compares values and
  types, shares `len`'s closed calls (and `ph 5`'s) between functions at
  every `α`. Instances per type made one closed term per type, so a trace
  in them printed once per type (`RtCseClosed`, `hidden`, `phantom`). The
  type shows only behind `lcAny`, so the instance at a concrete type read
  what `lcAny` hides at that type (the A833 class, previous entry); the
  instance at `lcAny` is the uniform code, as natively.
- **Where:** `Mono.lean`: `typeParamHidden`, `renameApp` (`L2R_DEBUG_HIDDEN`
  prints each call it changes), `keepsInstance`;
  plan [§2.3](../../translation-plan.md#23-instances); tests
  `RtCseClosed`, `RtCseHiddenAny`.
- **Remove only if:** never: it is the representation native Lean uses.

### A type argument whose values are types gets `lcAny`

- **What:** At a call of a definition (not an extern), a type argument that
  is itself a sort or a function type into a sort (`Type`, `Type → Type`,
  `Prop`: `isTypeFormerType`), whose values are types, is replaced by
  `lcAny` in the instance key (`renameApp`). Example: `apTwice {α : Type u}
  (f : α → Nat) (x y : α)` called as `apTwice k2 Nat Nat` (`α := Type`)
  calls `apTwice` at `lcAny`, with `x y : lcAny` given `box(0)`.
- **Why:** Natively the function is one, with `x y : lcAny`: data
  parameters. At `α := Type` the instance's `x y : Type` are type
  parameters for Lean's passes: `toMono` erases them and their uses,
  `reduceArity` removes them, and `cse` merged `f ◾` and `f ◾`, so a trace
  or panic in `f` ran once instead of twice (adversarial review of the
  dependent-type work: K3, K2, TypesAsData). A proposition as the type
  argument already gave `lcAny` (it is erased in LCNF, so the argument is
  not statically known); a parameter that is a proof (`{p : Prop} (x : p)`)
  is erased in the declaration itself, natively too.
- **Where:** `Mono.lean`: `renameApp`; plan
  [§2.3](../../translation-plan.md#23-instances); test `RtTypesAsValues`.
- **Remove only if:** Stage 1 stops making an instance per type argument.

### `Decidable.decide` keeps its name

- **What:** Calls of `Decidable.decide` are not redirected to an instance.
- **Why:** Lean's `toMono` replaces `Decidable.decide` by its argument,
  recognizing it by name. An instance under a new name survived as a call,
  which blocked the folding of the `if` on it and of the closed terms
  around it (adv2 PRG-02, fbf37e8).
- **Where:** `Mono.lean`: `renameApp`.
- **Remove only if:** Lean's `toMono` stops recognizing it by name.

### Static dictionaries specialize their callee

- **What:** A dictionary built only from instance constants, types and
  projections of such is *static*. A callee receiving one gets an instance
  keyed by the dictionary too (`InstKey.dicts`). That instance rebuilds the
  dictionary as `let`s at its start and binds the parameter to it. The
  parameter itself stays, unused, so the arity is unchanged. A dictionary
  deeper than 64 is not static, nor is one holding a constant that is
  more than a dictionary of functions (`constComputes`, next entry); the
  callee reads that constant at run time, as natively.
- **Why:** Lean's base `simp` folds only dictionaries that are
  `let`-bound in the same function. `Monad Id`, passed as a parameter from
  `Array.map` to `Array.mapM`, would stay a runtime record with polymorphic
  methods, which Reussir cannot type. The depth bound stops polymorphic
  recursion from building ever larger dictionaries.
- **Where:** `Mono.lean`: `staticDict?`, `constComputes`, `dictLets`,
  `instantiate`, `renameApp`; plan [§2.4](../../translation-plan.md#24-type-classes).
- **Remove only if:** never: without it, type classes with polymorphic
  methods fall back to `Box`. The rebuilding is a known divergence (an
  instance's code may run more often than natively: plan
  [§10](../../translation-plan.md#10-known-divergences-and-unsupported-features),
  "Dictionary rebuilding"). Constants that are more than dictionaries of
  functions are excluded (next entry).

### Only a dictionary of functions is a static constant

- **What:** A zero-parameter constant is part of a static dictionary only
  if evaluating it builds nothing but the class's structure (and its
  parents'), closures, constructors without relevant fields and small
  numbers (`constComputes`). A function call, a constructor of a non-class
  type with a relevant field (a list or record literal, `Thunk.mk`), a
  string literal or a number from 2^63 on makes it a runtime value.
  `cases` and join points count as computing; other constants are followed
  8 deep.
- **Why:** Natively such a constant is evaluated once at startup and a
  callee Lean did not specialize (`Inhabited` is `weak_specialize`) reads
  its fields. Specialized on it, the callee got the constant's body copied
  by `simp` (`inlineProjInst?`) and ran it at every call: the call again
  (round 7 RV7F-02: 4.3 s for 0.00 s), the literal rebuilt, a new thunk
  forced again (RV7F-04: "forced" 4 times for once). Only methods gain from
  the copy.
- **Where:** `Mono.lean`: `constComputes`, `staticDict?`; plan
  [§2.4](../../translation-plan.md#24-type-classes), §10 "Dictionary
  rebuilding"; test `RtDictConst`.
- **Remove only if:** Stage 1 stops specializing on dictionaries Lean
  passes at run time, or its `simp` stops copying instance bodies into
  callees.

### Stage 1's `simp` does not inline definitions

- **What:** Lean's base `simp` runs on every instance with
  `inlineDefs := false`: it folds dictionary projections
  (`inlineProjInst?`), but does not inline other definitions. General
  inlining happens in Stage 2, over lean2rr's own instances.
- **Why:** Persisted bodies may contain type-unsafe code (see
  [uniform-types.md](uniform-types.md#lean-library-code-that-relies-on-the-uniform-representation)).
- **Where:** `Mono.lean`: `monoInstance`.
- **Remove only if:** Stage 1 never meets type-unsafe persisted bodies.

### Polymorphic externs get typed extern instances

- **What:** An extern with type parameters (`Array.push {α}`) gets an
  instance at the call's type arguments that is still an extern (the plan
  writes `Array.push@Nat`; the real name is `Array.push._l2r.k`). Its signature is built from the declaration's type,
  and borrow annotations are dropped. A monomorphic extern keeps its own
  name.
- **Why:** The lowering needs the element type to choose storage types;
  Lean's constant folding recognizes monomorphic externs by name.
- **Where:** `Mono.lean`: `instantiateExtern`, `renameApp`
  (`monoExterns`); plan
  [§2.5](../../translation-plan.md#25-local-polymorphic-functions-and-externs).
  Storage rules: [../externs-ffi/glue.md](../externs-ffi/glue.md#extern-instances-pass-values-in-their-storage-type).
- **Remove only if:** never.

### `initialize` constants are read, not instantiated

- **What:** A reference to a constant defined by `initialize c : T ← act`
  is not redirected: `act`'s function becomes a root, and Stage 4 reads
  `c` from a once-cell filled at startup.
- **Why:** Such a constant has no code; its value is what `act` returned
  when the module was initialized.
- **Where:** `Mono.lean`: `renameApp` (`initConsts`); `Lower/Decls.lean`:
  `Callee.initConst`; `Emit/Startup.lean`: `startupChain`. See
  [../startup/constants.md](../startup/constants.md).
- **Remove only if:** never.

### Extern calls are redirected to Lean definitions where Lean has them

- **What:** Stage 1 redirects a call of an extern whose C symbol some
  Lean definition exports (`@[export sym]`) to that definition, and a call
  of any definition that lean2rr's shim replaces (`l2r_override_<mangled
  name>`) to the shim's.
- **Why:** See [../externs-ffi/dispatch.md](../externs-ffi/dispatch.md).
- **Where:** `Mono.lean`: `redirectTarget`, `exportMap`.
- **Remove only if:** see the linked entries.

### The `IO.Error` builders become roots on demand

- **What:** When the program reaches a fallible IO extern (files,
  processes), Stage 1 instantiates Lean's exported `lean_mk_io_error_*`
  builders.
- **Why:** The runtime reports errors as a kind number; the glue builds
  the `IO.Error` with Lean's own builder for that kind, as
  `decode_io_error` does (see
  [../externs-ffi/glue.md](../externs-ffi/glue.md#fallible-io-uses-a-last-error-slot-and-leans-own-error-builders)).
- **Where:** `Mono.lean`: `ensureIOErrorBuilders`, `ioErrorBuilderSyms`,
  `isFallibleIOSym`, `processIOSyms`.
- **Remove only if:** never.

### Type-unsafe library code is kept, not recompiled from source

- **What:** Stage 1 can redirect type-unsafe `implemented_by` targets
  (`Array.mapMUnsafe`) to their safe declarations and recompile the
  callers they taint from source, but this is off:
  `MonoConfig.safeSources := false`, with no command-line switch. (The
  recompilation itself, `recompile` with `recompilePasses`, is still used
  for a safe declaration whose `implemented_by` leaves it no persisted
  body.)
- **Why:** Recompiling loses Lean's inlining and specialization in those
  callers. lean2rr represents the unsafe code instead (see
  [uniform-types.md](uniform-types.md#lean-library-code-that-relies-on-the-uniform-representation)).
- **Where:** `Mono.lean`: `MonoConfig.safeSources`, `redirectTarget`,
  `isTainted`, `isTypeUnsafeImpl`, `baseDeclFor?`, `recompile`; plan
  [§2.7](../../translation-plan.md#27-library-code-that-relies-on-the-uniform-representation).
- **Remove only if:** the `safeSources` branches (the last case of
  `redirectTarget`, the `isTainted` check in `baseDeclFor?`) may be
  deleted; `recompile`/`recompilePasses` stay.
