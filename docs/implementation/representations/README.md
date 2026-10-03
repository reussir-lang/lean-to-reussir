# Representations

How each kind of Lean value is laid out in Reussir and in the runtime, and
the special cases behind those choices. The type table is in plan
[§5.1](../../translation-plan.md#51-type-translation); the runtime's side
is in [`runtime/README.md`](../../../runtime/README.md).

- [nat-int.md](nat-int.md): `Nat` and `Int` as one word in Lean's encoding
  (tagged handles, Reussir patch 0050), fast paths, big numbers as
  `lean_mpz_object`, literals, printing.
- [records.md](records.md): generated types for inductives: unit, value
  enums and structs, field order, hidden fields, names.
- [arrays.md](arrays.md): storage types, `ElemBox`, enumerations as
  indices, one-word `Nat`/`Int` arrays, capacities, indices.
- [strings.md](strings.md): the counted string, the string literal table
  and its `[` escape.
- [box-and-uniform.md](box-and-uniform.md): the uniform `Box` type and its
  variants.
- [placeholders.md](placeholders.md): Lean's `box(0)` as the zero of a
  type, the boxed unit `b0`.
- [function-values.md](function-values.md): function values as generated
  enums applied by generated functions.
- [references.md](references.md): `ST.Ref` as a record around a Reussir
  cell.
- [identity.md](identity.md): what `ptrAddrUnsafe` and `ptrEq` answer
  (identity and sharing are not preserved).

Thunk and task cells are in [../tasks/cells.md](../tasks/cells.md).
Conversions between representations are in
[../conversions/](../conversions/README.md).
