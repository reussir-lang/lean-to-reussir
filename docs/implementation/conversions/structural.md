# Structural conversions

Paths are relative to `lean2rr/LeanToReussir/` unless they start with
`runtime/`. Plan [§5.1](../../translation-plan.md#51-type-translation).

### Conversions are inserted wherever representations differ

- **What:** Call arguments, return values, constructor fields, join-point
  arguments, closure arguments and results, and the results of exact and
  over-applied calls go through `coerce` when their Reussir types differ.
  `coerce` tries `tryCoerce` (boxing, unboxing, function-value and lazy
  conversions, structural conversions, words), then a cast fallback;
  where no conversion exists it warns and emits a run-time panic.
- **Why:** Typed code meets uniform code (polymorphic recursion,
  existentials, Lean's `NonScalar` library code) and values merged by
  Lean's `cse` across types. The program is always translated (adc9180).
- **Where:** `Lower/Conv.lean`: `coerce`, `tryCoerce`, `castFallback`;
  `Lower/Decls.lean`: `lowerArg`.
- **Remove only if:** never.

### Instantiations of one inductive convert field by field

- **What:** Two instantiations of an inductive convert constructor by
  constructor; fields pair by Lean field index, not record position. A
  field relevant in the target but not in the source (a `PLift` of a
  proof that one instantiation drops) gets the target's placeholder. A
  value converted to `L2RUnit` is evaluated and dropped.
- **Why:** Lean's mono `cse` compares erased types, so it can merge
  `[] : List Shape` with `[] : List Nat`; such a value has no data where
  the types differ, so rebuilding it at the target type always works
  (9ab9492). Field pairing by index and the placeholder: G04PLiftPair,
  B17Univ (354b5cc).
- **Where:** `Lower/Conv.lean`: `structConv`, `structConvBody`,
  `convArms`, `ConvArm`, `convBuild`.
- **Remove only if:** never.

### Deep values convert in loops, not by recursion

- **What:** A conversion whose recursion goes through one field of each
  constructor (a list's tail) is a directly recursive function, which
  Reussir runs as a loop (tail recursion modulo constructors). Any other
  recursion (several recursive fields, through other types such as a rose
  tree's `List` of trees or mutual inductives, through array elements) is
  an explicit-stack loop over the pending constructors (`convMachine`).
- **Why:** Converting a 10^6-level left spine overflowed an 8 MB stack;
  natively nothing is converted, so nothing uses stack (e8feb4a, test
  `RtConvDeep`).
- **Where:** `Lower/Conv.lean`: `convGroup`, `convSlots`, `ConvSlot`,
  `convMachine`, `structConvBody` (`selfOnly`).
- **Remove only if:** never.

### Values with the same layout are reinterpreted, not converted

- **What:** When two shared records or arrays have the same layout (the
  same constructors with fields of the same layouts, position by position,
  coinductively; arrays of such elements) and the conversion would pair
  exactly those fields, the value is used as it is: `l2r_retype`, a
  `transmute` of the handle. This covers instantiations that differ only
  in phantom positions and isomorphic inductives read through
  `unsafeCast` (a user list as `List`).
- **Why:** No time, no copy, and the value keeps its identity. An
  `Array T₁` field read at `Array T₂` was converted at every use
  (Rp4CastArr 13.8 s → 0.00 s, native 0.00 s; adv4 RP4-07, aefebc6).
- **Where:** `Lower/Conv.lean`: `retypable`, `retypableAux`,
  `structPair?`; `runtime/prelude.rr`: `l2r_retype`.
- **Remove only if:** never.

### Arrays convert element by element; impossible elements are unreachable

- **What:** Arrays whose element storage differs convert with a generated
  element-wise loop (`vecConv`). When the elements cannot be converted
  (`Array String` to `Array Nat`), the element step is `unreachable`: only
  an empty array (shared by `cse`, or the result of mapping nothing)
  reaches such a conversion. (The comment in `vecConv` and plan §5.1 still
  give `Array Nat` to `Array Int` as the example; since ca9b64d `Nat`
  converts to `Int`.)
- **Why:** Lean's uniform-representation library code reinterprets
  `Array α` as `Array NonScalar` and back (011966c).
- **Where:** `Lower/Conv.lean`: `vecCoerce`, `vecConv`;
  `LowerState.vecConvs`.
- **Remove only if:** never. Cost: a conversion copies (see plan
  [§10](../../translation-plan.md#10-known-divergences-and-unsupported-features),
  "Structural conversions").

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
