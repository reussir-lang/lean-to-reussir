# State machines (J4)

Paths are relative to `lean2rr/LeanToReussir/`. Plan
[§5.6](../../translation-plan.md#56-join-points), "J4".

### A loop through outlined join points is one state machine

- **What:** When an outlined join point of a self-recursive declaration
  tail-calls the declaration (in its body, or in a join point inlined into
  it), the declaration becomes one function `<f>_sm` over an enum of entry
  points `<f>_mode`: a variant for the declaration's own entry and one per
  outlined join point (its captured variables and parameters). The
  declaration's own function enters at its variant; self tail calls and
  jumps to outlined join points re-enter the state machine, all self tail
  calls, which LLVM turns into a loop. In the core form the entry variant
  carries the parameters, so a jump passes only its variant and keeps no
  value alive. The entry enum is shared, not `[value]`.
- **Why:** Without it, a loop through an outlined join point was mutually
  recursive and used stack per iteration (the classic Sieve and Strings
  overflowed a 1 GiB stack at their medium size with the join-point passes
  off; 3597a31). Reussir has no guaranteed tail calls. The enum is shared
  because Reussir loses bytes of `[value]` enums whose arms differ
  ([Reussir bug 1](../../../reussir-bugs/01-value-enum-payload.md)); its
  reuse makes the cell cheap. The "inlined into it" case was a loop of
  `Std.Http` that stayed mutually recursive (5585f99).
- **Where:** `Lower/StateMachine.lean`: `stateMachinePlan`,
  `hasSelfTailCall`, `outlinedBodies`, `withInlinedJps`,
  `stateMachineSelfCall`, `stateMachineJumpCall`, `emitStateMachine`;
  `Lower/Ctx.lean`: `StateMachine`, `JumpAction.enter`; `Lower/Code.lean`:
  `lowerCode` (the re-entry), `lowerDecl`. Required part
  `loop-state-machines` in `Opt/Registry.lean`.
- **Remove only if:** Reussir guarantees tail calls, or a multi-arm
  `[value]` enum and a mutual tail call both become free.

### State machines entered and re-entered without allocation (`state-machines`)

- **What:** The optional form makes every variant nullary: the
  declaration's parameters and the outlined join points' values are
  parameters of the `_sm` function, in slots, one per (type, position); a
  variable passed on under a parameter's name keeps that parameter's slot.
  A jump passes its values in their slots and placeholders in the others,
  never a live value; a String placeholder is one shared empty string
  (`l2r_str_shared_empty`, no once-cell). Jumps and self calls are lowered
  as `fn(values…, mode::v)` and put in slots when the machine is emitted
  (`smCall`).
- **Why:** The core form allocates a variant per call and per jump; jumps
  of the earlier form still built a 9-13-field heap variant and read
  placeholders (round 7 RV7L-03, 69ab202: allocation sites gone from the
  LLVM IR of LwSmPerf and LwOutSelf). Passing a live value twice would
  keep it referenced across the jump, so an array updated before the jump
  would be shared and copied at every iteration (probes J4Arr/J4For; RF-1,
  5c5f6fc). Test `RtJpSlots`.
- **Where:** `Opt/StateMachines.lean`: `slotLayout`, `smCall`,
  `slotPlaceholder`, `emitStateMachineAlongside`, `alongsideSelfCall`,
  `alongsideJumpCall`, `alongsideForm`; hook `LowerHooks.stateMachine`
  (`StateMachineHook`), which tags the planned form
  (`StateMachine.form`); `runtime/leanrt/src/string.rs`: `shared_empty`.
  Plan §5.6 (J4).
- **Remove only if:** the pass is off (the core form allocates), or a
  `[value]` mode enum (Reussir bug 1 fixed) is shown as cheap in the IR.

### No slot for a type whose placeholder is not a finite value

- **What:** `slotLayout` gives a type a slot only if its placeholder's
  generated code never reaches `l2r_unreachable` (`placeholderFiniteE`);
  a field of another type stays in its variant, which is then allocated.
- **Why:** A slot's placeholder is evaluated at every jump that does not
  fill it. `zeroValue` builds `l2r_unreachable` for a type without a
  finite value, and inside a record whose first usable constructor holds
  one (`inductive W | bad (e : Empty) | ok (n : Nat)`); the earlier form
  passed placeholders for every parameter, so such a loop stopped with
  "INTERNAL PANIC: unreachable code has been reached" at its first jump
  (found with RV7L-03, test `RtJpSlots`).
- **Where:** `Opt/StateMachines.lean`: `slotLayout`,
  `placeholderFiniteE`/`placeholderFiniteB`.
- **Remove only if:** `zeroValue` always builds a finite value (and slots
  never hold an uninhabited type).
