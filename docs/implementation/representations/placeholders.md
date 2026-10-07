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
  Every placeholder found is kept (`zeroFns`): it is a finite value of its
  type, built from finished functions, whatever was avoided to find it.
  That there is none is kept (`zeroNone`) only if the search avoided no
  enclosing type. Only a type without a
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
  RV9C-01, tests `RtZeroFinite`, `RtZeroLazyCycle`). Keeping only the
  results that avoided no enclosing type rebuilt a nested shape's
  placeholders per occurrence, exponentially (C01R-02).
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

- **What:** `box(0)`, the box word 1 (`l2r_any_unit`), unwraps to the
  zero of whatever type it is read at (`boxUnbox`'s 0 arm, leanrt's kinds
  in `leanrt::any`). A unit value boxed is that word, no allocation: the
  value of every `IO Unit` result is a boxed unit (`EST.Out.ok`'s field is
  a `Box`).
- **Why:** A unit used at another type is natively `box(0)`. Before, a
  boxed unit read at another type hit `unreachable` (829f20a). One shared
  placeholder saves an allocation per `IO Unit` result, and all boxed
  units then have one address, as natively all are the scalar `box(0)`.
- **Where:** `Lower/Conv.lean`: `unboxMatch`, `tryCoerce` (the unit case);
  `Lower/Finish.lean`: `finishUnboxFns`.
- **Remove only if:** never.

### A placeholder put in a box is `box(0)`

- **What:** When a placeholder of a type `t` (`zeroValue`, the generated
  `l2r_zero_N` of `t`, in line or bound to a variable) is boxed, the box
  is `box(0)` (`l2r_any_unit`), not `t`'s zero boxed (`boxOf`, the box
  branch of `tryCoerce`). This is the core translation, not a pass.
- **Why:** Natively the placeholder is `box(0)`. `Array.modify` stores
  `unsafeCast ()` in the slot it updates: on an `Array Float` the unit
  became `0.0` (the coercion of a unit-like value to `Float`), then a new
  `Float` cell when stored in the array, two cells per update instead of
  native's one (adversarial review of the dependent-type branch, finding 2;
  test `RtDepFloatArrayAlloc`, modes `modify`, `set`, `modw`). `box(0)`
  reads back as `t`'s zero at every type: leanrt's kinds and the scalars
  decode the word 1 as their zero, and a program type's unboxing splits
  the word first, the 0 arm giving `t`'s zero or its variant 0 when that
  one is nullary (`boxUnbox`, "A boxed unit is Lean's `box(0)`" above), the
  same value as `zeroTry` picks (the first constructor without fields).
  Mode `zero` of the test reads `unsafeCast ()` back through an array at
  `Nat`, `Bool`, `Option Nat` and `UInt32`.
- **Where:** `Lower/Conv.lean`: `boxOf`; `Lower/Code.lean`:
  `closedLetValue` (a `let` of `◾`).
- **Remove only if:** never.

### Placeholders that allocate are built once

- **What:** With the optional pass `placeholder-cache`, a placeholder
  that would allocate (a string, an array, a record, a reference, a boxed
  unit) is kept in a once-cell like a constant, but without the
  constant's walk for tasks (`cafAccessor`'s `walk := false`); nullary
  values (a nullary constructor, a function value's `z`) are not cached:
  they do not allocate.
- **Why:** `Array.modify` stores one placeholder per update: on
  `Array (Array Nat)` that allocated an empty array per update (F07,
  829f20a). A placeholder is never inspected, so a shared value does as
  well as a fresh one. Natively a placeholder is `box(0)`, which
  `lean_mark_persistent` never sees; walking it ran the never-forced
  `pending` task cell a placeholder can hold, whose `z` function asked for
  the placeholder being built, and hung the program (C01R-01, test
  `RtZeroTaskCycle`). The walk of a constant also skips such a cell
  wherever it meets it (`pending` with the `z` function value: a
  reference `ST.Ref.take` left holding a placeholder), as native skips
  `box(0)` (C01R-03, tests `RtZeroWalkRef`, `RtZeroWalkRefNoCache`).
- **Where:** `Lower/Conv.lean`: `zeroTry`, `cafAccessor`;
  `Opt/PlaceholderCache.lean`; `LowerCtx.cachePlaceholders`.
- **Remove only if:** the pass is off; then each placeholder is built
  where it is used.

### Where lean2rr itself passes placeholders

- **What:** lean2rr also emits placeholders of its own where a value must
  be passed but is never read: the parameters passed beside a state
  machine's join-point variant
  ([../control-flow/state-machines.md](../control-flow/state-machines.md#state-machines-entered-without-allocation-state-machines)),
  a field of a cast's target that reads nothing of its source
  ([../conversions/casts.md](../conversions/casts.md#fields-pair-by-native-layout-slot)),
  a field of a parameter's type when the parameter is a proof or a type
  ([records.md](records.md#an-inductive-has-one-type-whatever-its-arguments)),
  and the value `ST.Ref.take` leaves in the cell
  ([references.md](references.md#take-moves-the-value-out-of-the-cell)).
- **Why:** Passing a live value instead would keep it alive (and shared)
  across the call.
- **Where:** see the linked entries.
- **Remove only if:** see the linked entries.
