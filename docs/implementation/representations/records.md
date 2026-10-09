# Generated types for inductives

Every inductive becomes one generated Reussir type (`nominalType`),
mirroring the Lean declaration, whatever its type arguments. Paths are
relative to `lean2rr/LeanToReussir/` unless they start with `runtime/`.
Plan [§5.1](../../translation-plan.md#51-type-translation).

### An inductive has one type whatever its arguments

- **What:** `nominalType` computes the fields of each constructor once,
  from their declared types with every parameter of the inductive
  `lcAny`, through Lean's `toMonoTypeKeep`: a field `x : α` is a `Box`,
  `xs : List α` is the one `List` type, `f : α → β` is the function type
  `Box → Box`, a concrete field (`n : Nat`, `x : Float`) keeps its type.
  `Tree Nat` and `Tree α` are one type, keyed by the inductive
  (`LowerState.typeNames`; `typeHeads` gives the inductive back). A field
  of a parameter's type is a `Box` at every instantiation, also where the
  parameter is a proof or a type: it then holds `box(0)`, as natively.
  `uniformType` is that type.
- **Why:** Native Lean does the same: a field of unknown type is one
  `lean_object*`. With one type per instantiation, a value crossing into
  uniform code was rebuilt node by node (exponential on shared data:
  [../conversions/structural.md](../conversions/structural.md#a-value-of-an-inductive-is-never-rebuilt)),
  and polymorphic recursion in a type needed a cut (Lean 4.33's growing
  parameters; Lean 4.34 accepts only growing indices, which mono erases).
  Typed code keeps precise types for its own values (Stage 3 types
  parameters, results and locals): only data layouts are uniform.
- **Where:** `LowerBase.lean`: `nominalType`, `uniformType`; plan
  [§5.1](../../translation-plan.md#51-type-translation).
- **Remove only if:** never.

### A field is read at its binder's type, once

- **What:** A `cases` binds each field parameter at the parameter's own
  Reussir type (`lowerType p.type`, which Stage 3 refines): a `Box` field
  read by a parameter of type `Nat` is unboxed in a `let` right after the
  match, not at each use. A parameter the declaration never uses is not
  converted (`CodeCtx.used`, `codeUses` of the body), nor one of a unit
  type (it carries nothing). The match's binders keep the record's
  values, which `fresh-rebuild` rebuilds the matched value from; the
  fields `lazy-fields` binds later are converted where it binds them.
  Where such a parameter goes back to a position of the field's type (a
  field of a rebuilt constructor) and also has another use, the code boxes
  its value again; it does not pass the field's own box. A parameter whose
  every use puts it back into a box is not converted at all: it keeps the
  field's box (`CodeCtx.boxedOnly`,
  [box-and-uniform.md](box-and-uniform.md#a-value-that-only-goes-back-into-boxes-keeps-its-box)).
  A binding drops a conversion's `let` that
  its code does not use (`dropUnusedConvs`, `CodeCtx.fieldConv`): enum and
  structure arms, and the later bindings of `lazy-fields`, whose consuming
  re-match also keeps a conversion made while the value was live instead
  of unboxing that field again.
- **Why:** With one type per inductive, the fields of a parameter's type
  are `Box`es; binding them at the record's type made every use of a
  `Nat` field unbox again. With the one-word box, a new box of a pointer
  payload or of a small scalar allocates nothing (only a `Float`, a
  `UInt64` from 2^63 and an `ElemBox` are cells). Passing the field's own
  box instead (commit 3f0cb30, reverted) left the unboxed value dead in
  the rebuilding branch, and Reussir's token reuse took its release (which
  never frees) as the donor of the new node instead of the matched cell:
  `RtProbeBump`, an association list of pairs bumped in a loop, allocated
  a list cell per rebuilt node (Reussir
  [issue 39](../../../reussir-bugs/39-alias-release-donor.md), a missed
  optimization). A new box leaves no such release. A parameter that is
  only boxed again has no unboxed value, so there is no dead release
  either (`RtProbeBump` stays at native's allocations).
- **Where:** `Lower/Hooks.lean`: `bindField`, `bindStructFields`;
  `Lower/Ctx.lean`: `CodeCtx.fieldConv`;
  `Lower/Code.lean`: `lowerCases` (enum and structure arms),
  `dropUnusedConvs`, `fieldConvNames`, `lowerDecl` (`used`);
  `Opt/LazyFields.lean`: `lazyStructFields`, `lazyLowerAlt`
  (`LazyMatch.fields` carry the parameter's type); projections
  (`Lower/Values.lean`: `lowerLetValue`, `.proj`) convert to the binder's
  type at once.
- **Remove only if:** never.

### Unit-like values are the value enum `L2RUnit`

- **What:** `Unit`, `PUnit`, `◾` (erased values) and the IO world
  `lcVoid` are `enum [value] L2RUnit { u }` from the prelude. Erased
  parameters are removed (rule 4), except a function's last parameter,
  which stays one `L2RUnit` parameter for its trailing erased ones and
  receives `L2RUnit::u{}`
  ([../control-flow/calls-and-lets.md](../control-flow/calls-and-lets.md#erased-parameters-are-removed-rule-4));
  an erased domain of a function type is a unit domain or a phantom one
  ([function-values.md](function-values.md#erased-domains-of-function-types-are-unit-or-phantom-rule-4)).
  The world and `Unit` are values: their parameters stay.
- **Why:** Reussir's own `unit` is result-only: it cannot be stored or
  passed. The unit kept for trailing erased parameters keeps the point
  where Lean runs the body
  ([../types/instances.md](../types/instances.md#instances-keep-leans-arity-stage-1)).
- **Where:** `RR.lean`: `Ty.unit`, `Expr.unitVal`; `LowerBase.lean`:
  `lowerTypeApp`; `ErasedDomains.lean`: `keepMask`;
  `Lower/Externs.lean`: `externParamPassed`;
  `runtime/prelude.rr`: `L2RUnit`.
- **Remove only if:** Reussir's `unit` becomes a value type.

### Three shapes, and value enums only without fields

- **What:** An inductive with no relevant field anywhere is an
  `enum [value]` (no allocation); one constructor is a `struct`; anything
  else is a shared `enum`. An inductive with no constructors gets a single
  variant `c_impossible`. The only `[value]` enums lean2rr emits are these
  field-less enumerations and the entry enums of state machines whose
  variants are all nullary
  ([../control-flow/state-machines.md](../control-flow/state-machines.md#the-entry-enum-of-nullary-variants-is-a-value-enum-state-machines))
  (`Nat`/`Int` are one-word tagged handles,
  [nat-int.md](nat-int.md)); multi-field value records are `[value]` structs
  (join-point tuples), whose padding is explicit.
- **Why:** Reussir moves a `[value]` enum as its tag plus one
  representative arm, so bytes of another arm that fall on padding or on a
  `bool` are lost ([Reussir bug 1](../../../reussir-bugs/01-value-enum-payload.md)).
- **Where:** `LowerBase.lean`: `nominalType` (`Shape`), `tupleType`;
  plan [§9](../../translation-plan.md#9-open-items).
- **Remove only if:** bug 1 is fixed; then multi-arm value enums and value
  J4 entry enums with fields become possible.

### One-field structures are value structs

- **What:** A structure with a single relevant field (`ST.Out`, the result
  of every `BaseIO` call once the world is gone) is a `[value]` struct,
  unless its field's type is being translated at the same time (no type
  contains itself by value). Identity (`ptrAddrUnsafe`) and cast reads
  treat it as its field; once-cells, which need a type that crosses the
  FFI boundary, wrap it in an `ElemBox` (`TypeInfo.value`; arrays and
  references hold `Box`es).
- **Why:** No heap cell per `BaseIO` result (an `IO.Ref` loop: 0.25 s →
  0.17 s, 2f0255e); natively Lean represents such a structure by its
  field.
- **Where:** `LowerBase.lean`: `nominalType` (after its fields are
  lowered: a field type being translated has a name, `typeHeads`, but no
  `typeInfos` yet); `Opt/ValueStructs.lean`. Optional pass
  `value-structs` ([../optional-passes.md](../optional-passes.md)).
- **Remove only if:** the pass is off; then such structures are shared
  records like the others.

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
