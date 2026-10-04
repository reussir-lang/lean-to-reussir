# Generated types for inductives

Every inductive instantiation becomes one generated Reussir type
(`nominalType`), mirroring the Lean declaration. Paths are relative to
`lean2rr/LeanToReussir/` unless they start with `runtime/`. Plan
[§5.1](../../translation-plan.md#51-type-translation).

### Unit-like values are the value enum `L2RUnit`

- **What:** `Unit`, `PUnit`, `◾` (erased values) and the IO world
  `lcVoid` are `enum [value] L2RUnit { u }` from the prelude. Erased
  parameters stay parameters of type `L2RUnit` in declarations and closures
  and receive `L2RUnit::u{}`; only extern calls drop them.
- **Why:** Reussir's own `unit` is result-only: it cannot be stored or
  passed. Keeping erased parameters keeps Lean's arities
  ([../types/instances.md](../types/instances.md#instances-keep-leans-arity)).
- **Where:** `RR.lean`: `Ty.unit`, `Expr.unitVal`; `LowerBase.lean`:
  `lowerTypeApp`; `Lower/Externs.lean`: `externParamPassed`;
  `runtime/prelude.rr`: `L2RUnit`.
- **Remove only if:** Reussir's `unit` becomes a value type.

### Three shapes, and value enums only without fields

- **What:** An inductive with no relevant field anywhere is an
  `enum [value]` (no allocation); one constructor is a `struct`; anything
  else is a shared `enum`. An inductive with no constructors gets a single
  variant `c_impossible`. The only `[value]` enums lean2rr emits are these
  field-less enumerations (`Nat`/`Int` are one-word tagged handles,
  [nat-int.md](nat-int.md)); multi-field value records are `[value]` structs
  (join-point tuples), whose padding is explicit.
- **Why:** Reussir moves a `[value]` enum as its tag plus one
  representative arm, so bytes of another arm that fall on padding or on a
  `bool` are lost ([Reussir bug 1](../../../reussir-bugs/01-value-enum-payload.md)).
- **Where:** `LowerBase.lean`: `nominalType` (`Shape`), `tupleType`;
  plan [§9](../../translation-plan.md#9-open-items).
- **Remove only if:** bug 1 is fixed; then multi-arm value enums and value
  J4 entry enums become possible.

### One-field structures are value structs

- **What:** A structure with a single relevant field (`ST.Out`, the result
  of every `BaseIO` call once the world is gone) is a `[value]` struct,
  unless its field's type is being translated at the same time (no type
  contains itself by value). Identity (`ptrAddrUnsafe`) and cast reads
  treat it as its field; arrays, once-cells and references, which need a
  type that crosses the FFI boundary, wrap it in an `ElemBox`
  (`TypeInfo.value`).
- **Why:** No heap cell per `BaseIO` result (an `IO.Ref` loop: 0.25 s →
  0.17 s, 2f0255e); natively Lean represents such a structure by its
  field.
- **Where:** `LowerBase.lean`: `nominalType` (`predictValue`,
  `inProgressType`); `Opt/ValueStructs.lean`. Optional pass
  `value-structs` ([../optional-passes.md](../optional-passes.md)).
- **Remove only if:** the pass is off; then such structures are shared
  records like the others.

### Whether a type is a shared record is decided before its fields

- **What:** Before translating an inductive's fields, `nominalType`
  predicts from the constructor shapes whether the type will be a boundary
  type (a shared record) and records it in `pendingBoundary`, which
  `isBoundaryTy` consults for types in progress.
- **Why:** A field `Array Tree` inside `Tree` was translated while `Tree`
  was unknown, so it became `RVec<ElemBox(Tree)>`, while `Array Tree` is
  `RVec<Tree>` everywhere else: every `get!`, `size` or `push` of the field
  converted the whole array (Rp3MinArrSelf 1e5: 4.36 s → 0.00 s; adv3
  RP3-6, d6dd848). The `[value]` decision follows the same prediction, so
  the two cannot disagree; mutual types work whichever is translated first.
- **Where:** `LowerBase.lean`: `nominalType`, `isBoundaryTy`,
  `inProgressType`, `LowerState.pendingBoundary`.
- **Remove only if:** never.

### Fields are ordered by decreasing alignment

- **What:** Each constructor's relevant fields are placed in its record by
  decreasing alignment, ties in declaration order; `CtorLayout` maps each
  Lean field to its record position, and constructions, patterns,
  projections and conversions go through it. The driver turns Reussir's own
  member packing off.
- **Why:** Records without padding (rbtree memory 1.17x → 1.00x native,
  7860807); and Reussir's in-place variant reuse with packed layouts skips
  stores of fields packing moves
  ([Reussir bug 2](../../../reussir-bugs/02-reuse-field-store.md),
  variants half, unpatched), so packing must stay off and lean2rr does the
  ordering itself.
- **Where:** `LowerBase.lean`: `nominalType`, `fieldAlign`,
  `CtorLayout.place`, `CtorLayout.posTys`; `Opt/FieldOrder.lean`:
  `alignmentOrder`; `scripts/l2r.py` (`--no-pack-record-members`).
- **Remove only if:** the optional pass `field-order` may be turned off
  (then Reussir lays padding out as bytes); `--no-pack-record-members`
  stays until bug 2's variant half is fixed. See
  [../reussir-workarounds/correctness-bugs.md](../reussir-workarounds/correctness-bugs.md#bug-2-in-place-reuse-skips-a-field-store).

### Types with computed fields use their implementation inductive

- **What:** A type with computed fields (`Lean.Name`) is translated as its
  `T._impl` inductive, whose constructors also store the computed fields;
  variant names are relative to the type (`T.c._impl`).
- **Why:** Lean's runtime does the same, and mono code uses both names
  for the same values.
- **Where:** `LowerBase.lean`: `lowerTypeApp`, `nominalType`.
- **Remove only if:** never.

### Propositions have no representation

- **What:** A `Prop`-valued inductive is the unit type, and proofs are not
  passed to externs (a parameter declared at a type variable is passed even
  when instantiated at a proof-like type: `Array.push` at `PLift True`).
- **Why:** Proofs carry no data; the runtime's C-symbol functions take no
  proof arguments (runtime request 2; G01PushUnit, 354b5cc).
- **Where:** `LowerBase.lean`: `lowerTypeApp`; `Lower/Externs.lean`:
  `isPropTy`, `typeVarUses`; `Lower/ExternCall.lean`: `lowerExternCall`.
- **Remove only if:** never.

### `IO.Process.Child` has two hidden fields

- **What:** The generated record for `IO.Process.Child` has, after its
  three Lean fields, the pid (`u32`) and whether the child was spawned with
  `setsid` (`bool`). Only the process glue sets and reads them.
- **Why:** Native Lean's `Child` object carries them after its Lean fields
  (`process.cpp`); `wait`, `tryWait` and `kill` need them, and Lean code
  cannot build a `Child` (its constructor is private).
- **Where:** `LowerBase.lean`: `nominalType`; `Lower/Process.lean`:
  `spawnedChild`, `structField`, `processExtern`. See
  [../externs-ffi/glue.md](../externs-ffi/glue.md#child-processes-are-glue-over-runtime-primitives).
- **Remove only if:** never.

### Generated names are counters with an injective escape

- **What:** A generated type is `T_<hint>_<counter>`, its variants
  `c_<constructor>` with the constructor's name relative to the type,
  mangled with Lean's own name mangling (`c_…`, as declarations are
  `l_…`), which has a demangler and so never maps two names to one; other
  generated identifiers escape injectively (`identEscape`: `_` → `__`,
  other non-alphanumerics → `_<hex>_`).
- **Why:** Names must be valid Reussir identifiers that never clash with
  runtime or `std` names; uniqueness comes from the counter (constructor
  names once clashed: adv round 1, 3f59239). Printed and escaped,
  `«a.b»` and `a.b` became the same variant and rrc rejected the program
  (review RV9L-01, test `RtCtorNameClash`); Lean also prints pseudo-syntax
  roots (`«?a.b»`), inaccessible names (`✝`) and macro scopes unescaped
  (RV9L-01a), so only mangling is injective.
- **Where:** `LowerBase.lean`: `identEscape`, `nameHint`, `fnName`,
  `nominalType`; plan [§5.13](../../translation-plan.md#513-names).
- **Remove only if:** never.
