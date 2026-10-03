# The uniform type `Box`

A value whose type is `lcAny` in a relevant position (see
[../types/uniform-types.md](../types/uniform-types.md)) is stored as
`L2RBox`. Typed code never pays for it. Paths are relative to
`lean2rr/LeanToReussir/`. Plan
[§5.1](../../translation-plan.md#51-type-translation), "The uniform type
`Box`".

### `Box` has one variant per boxed type, made on demand

- **What:** `L2RBox` is a generated enum with one variant `b<n>(T)` per
  concrete Reussir type the program ever boxes, created as lowering needs
  them. It is always emitted, with at least the unit variant, which is
  created first and so is `b0`.
- **Why:** The set of boxed types is only known at the end of Stage 4;
  types can mention `Box` even when nothing is boxed (F05b: "unknown type
  L2RBox", 829f20a). A boxed unit is Lean's `box(0)` (see
  [placeholders.md](placeholders.md#a-boxed-unit-is-leans-box0)).
- **Where:** `LowerBase.lean`: `boxName`, `boxVariant`;
  `Emit/Program.lean`: `lowerProgram` (`boxVariant .unit` first, the
  `boxItem`).
- **Remove only if:** never.

### `lcAny` arguments hold `Box`; a boxed value is matched at the uniform instantiation

- **What:** An inductive applied to `lcAny` is instantiated with `Box` in
  those positions (schematically, `Free lcAny Nat` is `Free_Box_Nat`);
  `uniformType` gives the instantiation with every relevant argument
  `lcAny`. A `cases` on a value held in a `Box` first converts it to that
  uniform instantiation.
- **Why:** The uniform instantiation accepts values boxed from every
  instantiation of the inductive (and, in a program that can cast, from
  the types a cast reads), so one match covers them.
- **Where:** `LowerBase.lean`: `lowerTypeApp`, `uniformType`;
  `Lower/Code.lean`: `lowerCases`.
- **Remove only if:** never.

### Unboxing functions are generated last, until the variants are stable

- **What:** Unboxing to a nominal type, an array type or a function type is
  a generated function (`l2r_unbox_T`, `l2r_unbox_arr_N`,
  `l2r_unbox_fn_T`) whose body is generated at the end, matching every
  `Box` variant that can hold a value of the target's Lean type. Generating
  a conversion can add variants (for fields), so the bodies are
  regenerated until the variant set stops growing, interleaved with the
  application functions of function values.
- **Why:** One Lean type has several Reussir representations (`List Nat`
  and a uniform `List Box`; `LNatArr` and an `RVec<Box>` built by
  uniform-representation code), so unwrapping must accept all of them.
- **Where:** `LowerBase.lean`: `unboxFn`, `unboxArrFn`;
  `Lower/FnValues.lean`: `unboxFnFn`; `Lower/Finish.lean`:
  `finishUnboxFns`; `Emit/Program.lean`: `lowerProgram` (the finishing
  loops). Which variants each one accepts:
  [../conversions/box-unboxing.md](../conversions/box-unboxing.md).
- **Remove only if:** never.

### References and function values keep their identity in a `Box`

- **What:** A function value is boxed under the variant of its own type,
  and so is a reference; neither is converted when boxed.
- **Why:** A function value that goes through uniform code and back is
  then the same object (no wrapper chain); a reference cannot be converted
  without losing aliasing, so operations on a boxed reference dispatch
  over the boxed reference types
  ([references.md](references.md#a-reference-in-a-box-is-used-through-a-generated-dispatch)).
- **Where:** `Lower/Conv.lean`: `coerce`; `Lower/Externs.lean`:
  `refBoxOpFn`, `finishRefFns`.
- **Remove only if:** never.
