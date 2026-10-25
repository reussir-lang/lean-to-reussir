# Representations

How each kind of Lean value is laid out in Reussir and in the runtime, and
the special cases behind those choices. The type table is in plan
[§5.1](../../translation-plan.md#51-type-translation); the runtime's side
is in [`runtime/README.md`](../../../runtime/README.md).

- [nat-int.md](nat-int.md): `Nat` and `Int` as one word in Lean's encoding; `--int-backend rcgmp`, Reussir's built-in integers (in progress)
  (tagged handles, Reussir patch 10-a), the named helpers that are the one
  place that knows the encoding, fast paths, normalization and the
  call-free equality of a small and a big `Int`, big numbers in one
  block (header and limbs), literals, printing.
- [records.md](records.md): generated types for inductives: unit, value
  enums and structs, field order, hidden fields, names.
- [arrays.md](arrays.md): the array of boxes (`RVec<Box>`), the one-block
  array and its `count == 1` release, capacities (mimalloc's size class),
  indices.
- [compact-arrays.md](compact-arrays.md): `Array S` of a scalar as
  `RVec<u8|u16|u32|u64|f32|f64>` (optimization `compact-arrays`): the
  storage kinds, the whole-program check, the typed `map` loops, a `match`
  on an array, the boxed `Array α` fields, the safety net, the
  alternatives considered.
- [typed-arrays.md](typed-arrays.md): `Array X` of a one-word counted type
  (a shared record or enum, `Nat`, `Int`, `String`, an array) as `RVec<T>`
  of its own type (optimization `typed-arrays`, clean step B1): the
  pointer kinds, the check they share with compact arrays, elements
  without observable releases only, a set's release of a replaced record
  by its own drop, the costs.
- [strings.md](strings.md): the counted string, its equality, the string literal table
  and its `[` escape.
- [box-and-uniform.md](box-and-uniform.md): the uniform `Box` type and its
  variants; the one-word box `LAny`, which every `Box` is.
- [placeholders.md](placeholders.md): Lean's `box(0)` as the zero of a
  type, the boxed unit `b0`.
- [function-values.md](function-values.md): function values as generated
  enums applied by generated functions.
- [references.md](references.md): `ST.Ref` as a record around a Reussir
  cell.
- [typed-cells.md](typed-cells.md): a reference whose cell holds the
  element's own type (optimization `typed-cells`, clean step B2): the cell
  kinds, the whole-program check over the instances of the reference
  primitives, `take`'s placeholder, why thunks, tasks and promises keep
  their cells of boxes, the costs.
- [identity.md](identity.md): what `ptrAddrUnsafe` and `ptrEq` answer
  (identity and sharing are not preserved).

Thunk and task cells are in [../tasks/cells.md](../tasks/cells.md)
(they keep one state type over `Box` each: [typed-cells.md](typed-cells.md#thunks-tasks-and-promises-keep-their-cells-of-boxes)).
Conversions between representations are in
[../conversions/](../conversions/README.md).
