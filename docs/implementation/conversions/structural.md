# Structural conversions

Paths are relative to `lean2rr/LeanToReussir/` unless they start with
`runtime/`. Plan [§5.1](../../translation-plan.md#51-type-translation).

### Conversions are inserted wherever representations differ

- **What:** Call arguments, return values, constructor fields, join-point
  arguments, closure arguments and results, and the results of exact and
  over-applied calls go through `coerce` when their Reussir types differ.
  `coerce` tries `tryCoerce` (boxing, unboxing, function-value wrappers,
  casts between inductives, words), then a cast fallback; where no conversion exists it warns and emits a run-time
  panic.
- **Why:** Typed code meets uniform code (polymorphic recursion,
  existentials, Lean's `NonScalar` library code): a value goes into a
  `Box` field or comes out of one. The program is always translated
  (adc9180).
- **Where:** `Lower/Conv.lean`: `coerce`, `tryCoerce`, `castFallback`;
  `Lower/Decls.lean`: `lowerArg`.
- **Remove only if:** never.

### A value of an inductive is never rebuilt

- **What:** An inductive has one Reussir type whatever its type arguments
  (`nominalType`), so two binders of `List Nat` and `List α` hold the same
  value: nothing converts it; nor an array, a thunk or task, a reference
  (one type each, over `Box`). Only a cast between two *different*
  inductives can convert (`structConv`, [casts.md](casts.md)).
- **Why:** With one type per instantiation, a value that crossed into
  uniform code was rebuilt node by node, without memory of the nodes
  already rebuilt: a tree whose nodes share their children (`build n` with
  `.node t t`) took 2^(n+1) - 1 nodes (927 MB at n = 24, native 7.9 MB),
  and a loop that passed a structure to uniform code copied it at every
  iteration. Lean's mono `cse` merging `[] : List Shape` with
  `[] : List Nat` is now one value of one type.
- **Where:** `LowerBase.lean`: `nominalType`; plan
  [§5.1](../../translation-plan.md#51-type-translation).
- **Remove only if:** never.

### Values with the same layout are reinterpreted, not converted

- **What:** When the shared records of two different inductives have the
  same layout (the same constructors with fields of the same layouts,
  position by position, coinductively) and the conversion would pair
  exactly those fields, the value is used as it is: `l2r_retype`, a
  `transmute` of the handle. This covers isomorphic inductives read
  through `unsafeCast` (a user list as `List`: with one type per
  inductive, both hold `Box` elements). It takes nominal types only: an
  array, a thunk or task and a reference have one type each, so an
  `Array T₁` read at `Array T₂` is the same value without it.
- **Why:** No time, no copy, and the value keeps its identity. (Before
  arrays had one type, an `Array T₁` field read at `Array T₂` was
  converted at every use, and `retypable` covered arrays of such
  elements: Rp4CastArr 13.8 s → 0.00 s, native 0.00 s; adv4 RP4-07,
  aefebc6.) Casts between different inductives whose layouts differ keep
  their conversion (`structConv`, constructor by constructor: a `NatList`
  read as a `List Nat`), the one structural conversion left.
- **Where:** `Lower/Conv.lean`: `retypable`, `retypableAux`;
  `runtime/prelude.rr`: `l2r_retype`.
- **Remove only if:** never.

### Partial applications are built at the binder's type

- **What:** A partial application is built at its target's type (minus
  the supplied arguments, a `p` variant) and then converted to the type of
  the binder it is bound to: a `w<S>` wrapper, or boxed as it is for a
  `Box`. The target still runs only when its last argument arrives.
- **Why:** Lambda lifting can type a lifted lambda's result `lcAny` while
  its closure is used at `Nat × Int → Int`, or the reverse (F04 `maxBy?`,
  F05 range iterators; 829f20a, 3f59239; since 2a3f3c1 through function-value
  conversions instead of lambdas).
- **Where:** `Lower/Decls.lean`: `partialApp`; `Lower/FnValues.lean`:
  `partValue`; `Lower/Values.lean`: `lowerConstApp`; see
  [wrappers.md](wrappers.md#function-values-stay-one-wrapper-deep).
- **Remove only if:** never.
