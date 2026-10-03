# Stage 1: instances

Paths are relative to `lean2rr/LeanToReussir/` unless they say otherwise.

### Instances keep Lean's arity

- **What:** An instance keeps every type parameter of its declaration as
  an erased parameter, and its callers keep passing `◾` there. A partial
  application that stops before a type parameter calls the instance at
  `lcAny` for it; the parameter stays a parameter.
- **Why:** Arity decides when work runs (plan
  [§5.2](../../translation-plan.md#52-declarations-calls-arities)).
  Dropping type parameters turned a function with only type parameters
  into a zero-parameter constant, evaluated once at startup where Lean runs
  it at every use (review finding fixed in 4674426).
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
