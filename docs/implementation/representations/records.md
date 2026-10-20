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
  [issue 8](../../../reussir-bugs/08-alias-release-donor.md), a missed
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
  variant `c_impossible`. The program's types are `[value]` enums only
  when they have no fields. Two of lean2rr's own enums, whose values only
  pass from a call to a match, are `[value]` with fields too: the step
  enums of outlined recursive functions
  ([../control-flow/outline.md](../control-flow/outline.md#step-enums-are-value))
  and the entry enum of a `state-machines` state machine whose variant
  keeps a field (a state machine whose variants are all nullary has an
  integer entry point, not an enum:
  [../control-flow/state-machines.md](../control-flow/state-machines.md#the-entry-point-of-nullary-variants-is-an-integer-state-machines));
  the core form's J4 entry enum is shared, for its cost
  ([../control-flow/state-machines.md](../control-flow/state-machines.md#a-loop-through-outlined-join-points-is-one-state-machine)).
  `Nat`/`Int` are one-word tagged handles
  ([nat-int.md](nat-int.md)); multi-field value records are `[value]`
  structs (join-point tuples), whose padding is explicit.
- **Why:** A value of an inductive with fields is one heap object, as
  natively (one `lean_object*`): a copy is a count, it goes into a `Box`
  field without a new cell, and a matched cell can be reused in place. A
  recursive inductive (`List`, `Tree`) cannot be a `[value]` type. Until
  2026-10-19 lean2rr's own multi-arm enums were shared too (except the
  step enums whose layout a guard checked): Reussir lost bytes of `[value]`
  enums whose arms differ (old bug 1,
  [../reussir-workarounds/correctness-bugs.md](../reussir-workarounds/correctness-bugs.md#old-bug-1-value-enum-payloads-were-lost-when-moved)),
  fixed in lean2rr's base. That bug does not limit the program's types
  any more; a `[value]` representation for them would be a change of
  representation (boxing, conversions, reuse), not the removal of a
  workaround.
- **Where:** `LowerBase.lean`: `nominalType` (`Shape`), `tupleType`;
  plan [§9](../../translation-plan.md#9-open-items).
- **Remove only if:** never (the representation of the program's types).

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
  member packing off. Every tuple that lean2rr generates (`tupleType`: a
  J2 join point's tuple,
  [join points](../control-flow/join-points.md#a-j2-join-point-with-several-parameters-yields-a-value-tuple);
  a `flatten-structs` result `L2RFlat.Tuple<k>`,
  [optional passes](../optional-passes.md#structure-arguments-and-results-are-spread-into-their-fields-flatten-structs)) orders its
  members the same way, through the same function (`memberOrder`).
  `tupleType` finds a tuple type by its value types in the values' order
  and keeps its member order (`tupleOrders`); a construction lists the
  values in that order, and a projection of value `i` reads its member
  (`tupleLayout?`; `positionsOf` for a J2 tuple). The tuple of a `flatten-structs`
  result is returned, so it has no narrow member at its end: it keeps a
  `bool`, `u8`, `u16` or `u32` in a `u64` member (`tupleMemberTy`; a
  `bool` as 1 or 0, the others zero-extended; `toTupleMember`,
  `ofTupleMember`), and a unit value has no member (unless all its values
  are units; the projection gives the unit value). Its member order lists
  only the values it keeps. A J2 tuple is not returned and keeps its
  values' own types. Example: `String.Slice.toNat?` returns `Option Nat`,
  flattened to the tag and the value, `(bool, Nat)` in Lean's order; its
  tuple is `Tuple(u64, Nat)` (two members of 8 bytes, in the values'
  order), built as `Tuple{if t { 1 } else { 0 }, n}`, and a caller reads
  the tag as member 0 tested against 0. `Except String Unit × Array α`
  (Unionfind's monad) is `Tuple(u64, LStr, RVec<LAny>)`.
  A field's alignment (`fieldAlign`) is the one Reussir
  gives the member (`RR.fieldAlign?`, the model that the step variants of
  `outline` also use; Reussir's `memberStorageType` and
  `deriveCompoundLayout`). A `[value]` struct is laid out in place, so its
  alignment is the largest alignment of its fields, recursively. Example:
  with `struct [value] T_W(u8)` (a one-field structure that Lean keeps,
  such as one in a `mutual` block), `P.mk (w : W) (n : Nat) (b : UInt8)` is
  `T_P(Nat, T_W, u8)`, 16 bytes. Until 2026-10-19 every `[value]` struct
  counted as 8 bytes aligned: `T_P(T_W, Nat, u8)`, 24 bytes, 7 of them
  padding after `T_W`.
- **Why:** Records without padding (rbtree memory 1.17x → 1.00x native,
  7860807); and Reussir's in-place variant reuse with packed layouts skips
  stores of fields packing moves (a Reussir bug, fixed upstream in #656;
  the old stack has a local patch for it), so packing stays off and
  lean2rr does the ordering itself. A generated tuple: with
  `--no-pack-record-members`, Reussir widens a member that the next
  member's alignment pads (a `bool` before a `Nat`: an `i64`) and stores
  only the field's own bits, so LLVM keeps the tuple on the stack (issue
  17 of `reussir-bugs/`). Sorted `flatten-structs` tuples took
  MonadicInterp (n = 30000) from 21.95 to 21.73 billion instructions
  (−1.0%, cachegrind) and Liasolver (n = 50) from 13.58 to 13.49 billion
  (−0.7%). Sorted, a narrow member came last, and Reussir writes the
  padding at the end of a struct as explicit bytes (`{ ptr, ptr, ptr, i1,
  [7 x i8] }`): LLVM counts each byte as one more value of a returned
  struct, and on aarch64 a result of more than 8 values comes back in
  memory (`sret`; `(Nat, bool)` already has 9). Where the padding stays
  live (a result returned again as it is, as by a recursive call), the
  function then returned through the stack: Unionfind's `findEntryAux`
  ran 16% more instructions (dev b874c365; the program's median wall
  time went from 448 to 477 ms between timing runs 7 and 8). With
  whole-word members and no unit members (dev b874c365 → this rule,
  cachegrind, SVE-free builds, the benchmark arguments): Unionfind
  (n = 3000000) 9.397 → 8.256 billion instructions (−12.1%),
  MonadicInterp 21.758 → 20.351 billion (−6.5%), Liasolver −0.05%,
  Strings −0.07%, k-nucleotide −0.16%, Cedar (Z06g) −0.09%, the lean-zip
  cases Z01d and Z03d −0.01% or less, ClosurePipeline and ExprEval
  unchanged; the functions returned in memory (call sites that pass a
  stack slot in `x8`): Unionfind 2 → 0, MonadicInterp 7 → 0, Strings
  3 → 0, Liasolver 1 → 0, ExprEval 1 → 0.
- **Where:** `LowerBase.lean`: `nominalType`, `fieldAlign`, `layoutItem?`,
  `memberOrder`, `positionsOf`, `tupleType`, `tupleLayout?`,
  `tupleMemberTy`, `toTupleMember`, `ofTupleMember`, `tupleFields?`
  (`LowerState.flatTuples`),
  `CtorLayout.place`, `CtorLayout.posTys`; `Lower/Values.lean`:
  `lowerLetValue` (a `flatten-structs` tuple's constructor and
  projections); `Lower/Code.lean`: `lowerCode` (J2);
  `FieldAlign.lean`: `fieldAlign?`; `Opt/FieldOrder.lean`: `alignmentOrder`; `scripts/l2r.py`
  (`--no-pack-record-members`).
- **Tests:** `RtValueStructAlign` (`[value]` structs of sub-word fields in
  four records; its comment gives the layouts before and after);
  `RtFlattenNarrow` (`flatten-structs` results with `Bool`, `UInt8`,
  `UInt16`, `UInt32`, `Char` and `Unit` fields, the largest values,
  returned again by recursive calls).
- **Remove only if:** the optional pass `field-order` may be turned off
  (then Reussir lays padding out as bytes, and tuples keep the values'
  order); `--no-pack-record-members`
  is removable after the move to Reussir 7954a367, which fixes the
  variant half of that bug. See
  [../reussir-workarounds/correctness-bugs.md](../reussir-workarounds/correctness-bugs.md#old-bug-2-in-place-reuse-skipped-a-field-store).

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
