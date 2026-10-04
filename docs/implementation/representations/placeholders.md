# Placeholders: Lean's `box(0)`

Lean passes `box(0)` for values that are never inspected: an erased
argument (`◾`) at a relevant type, a unit-like value used at another type,
and the `unsafeCast ()` its library stores into an array slot so that the
element being updated stays unshared (`Array.modifyMUnsafe`,
`Array.mapMUnsafe`). Paths are relative to `lean2rr/LeanToReussir/`. Plan
[§2.7](../../translation-plan.md#27-library-code-that-relies-on-the-uniform-representation).

### A placeholder is the zero of its type

- **What:** `zeroValue t` is a generated function `l2r_zero_N`: `0`,
  `0.0`, `false`, `l2r_nat_small(0)`, the empty string or array, a
  constructor without fields, else the first constructor whose fields
  have zeros, a `done` cell holding a zero (a `pending` cell with the `z`
  function value, never forced, when the value has none), a new reference
  holding a zero. The search (`zeroTry`) is depth first: a type whose zero
  is being built (`zeroBusy`, with its depth) is not used for a field, and
  a constructor whose field has no zero is passed over for the next one.
  A result that avoided an enclosing type holds only there and is not
  kept; others are kept (`zeroFns`, `zeroNone`). Only a type without a
  finite value (`Empty`, a type each of whose constructors needs itself)
  gets `l2r_unreachable` (`zeroFinite` says so, also for the
  state-machines pass's slots).
- **Why:** For `Nat`, `Bool` and enumerations this is exactly what
  `box(0)` denotes natively; for other types the value is never inspected,
  so any value of the type will do, but it must be one: Lean's
  `Array.map`/`mapM`/`mapIdx`/`modify` store one in the slot they update,
  `IO.Ref.modify` (`ST.Ref.take`) leaves one in the reference. Taking the
  first constructor whose fields were not being built, without looking
  further, gave `inductive Term | app (p : Term × Term) | var (n : Nat)`
  the zero `app (l2r_unreachable)` and crashed those operations (round 9
  RV9C-01, tests `RtZeroFinite`, `RtZeroLazyCycle`).
- **Where:** `Lower/Conv.lean`: `zeroTry`, `zeroValue`, `zeroFinite`;
  `LowerState.zeroFns`, `zeroNone`, `zeroBusy`; `Opt/StateMachines.lean`:
  `slotPlaceholder?`. Plan §5.1.
- **Remove only if:** never.

### A function-typed placeholder is the `z` variant

- **What:** At a function type the placeholder is the nullary variant `z`
  of the function-value enum; applying it gives the zero of its result.
- **Why:** It is never applied natively; nullary costs no allocation.
- **Where:** `Lower/Conv.lean`: `zeroValue`; `Lower/Finish.lean`:
  `genApply`; see [function-values.md](function-values.md).
- **Remove only if:** never.

### A boxed unit is Lean's `box(0)`

- **What:** The unit variant of `Box`, `L2RBox::b0`, unwraps to the zero
  of whatever type it is read at; every unboxing function has that arm.
- **Why:** A unit used at another type is natively `box(0)`. Before, a
  boxed unit read at another type hit `unreachable` (829f20a).
- **Where:** `Lower/Conv.lean`: `unboxMatch`; `Lower/Finish.lean`:
  `finishUnboxFns`.
- **Remove only if:** never.

### Placeholders that allocate are built once

- **What:** With the optional pass `placeholder-cache`, a placeholder
  that would allocate (a string, an array, a record, a reference, a boxed
  unit) is kept in a once-cell like a constant; nullary values (a nullary
  constructor, a function value's `z`) are not cached: they do not
  allocate.
- **Why:** `Array.modify` stores one placeholder per update: on
  `Array (Array Nat)` that allocated an empty array per update (F07,
  829f20a). A placeholder is never inspected, so a shared value does as
  well as a fresh one.
- **Where:** `Lower/Conv.lean`: `zeroValue`, `cafAccessor`;
  `Opt/PlaceholderCache.lean`; `LowerCtx.cachePlaceholders`.
- **Remove only if:** the pass is off; then each placeholder is built
  where it is used.

### Where lean2rr itself passes placeholders

- **What:** lean2rr also emits placeholders of its own where a value must
  be passed but is never read: the parameters passed beside a state
  machine's join-point variant
  ([../control-flow/state-machines.md](../control-flow/state-machines.md#state-machines-entered-without-allocation-state-machines)),
  the source slot a split `map` loop writes back
  ([arrays.md](arrays.md#maps-that-change-the-element-representation-write-a-new-array)),
  a field relevant in a conversion's target but not in its source
  ([../conversions/structural.md](../conversions/structural.md#instantiations-of-one-inductive-convert-field-by-field)),
  and the value `ST.Ref.take` leaves in the cell
  ([references.md](references.md#take-moves-the-value-out-of-the-cell)).
- **Why:** Passing a live value instead would keep it alive (and shared)
  across the call.
- **Where:** see the linked entries.
- **Remove only if:** see the linked entries.
