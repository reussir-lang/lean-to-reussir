# State machines (J4)

Paths are relative to `lean2rr/LeanToReussir/` unless they start with
`runtime/`. Plan
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

### State machines entered without allocation (`state-machines`)

- **What:** The optional form makes every variant nullary: the
  declaration's parameters and every outlined join point's fields are
  parameters of the state machine's function, in slots, one per type and
  position (a variant's `i`-th field of type `T` goes in the `i`-th slot of
  type `T`; a variable passed on unchanged under a parameter's name keeps
  that parameter's slot). Each arm binds its fields from their slots. A
  call, a self tail call or a jump passes its values in their slots and a
  placeholder in every other slot (`zeroValue`'s, and for a string the
  runtime's one shared empty string), never a live value. Soundness guard,
  checked on every state machine: a type whose placeholder would reach
  `l2r_unreachable` (`inductive W | bad (e : Empty) | ok (n : Nat)`, whose
  placeholder is built from `bad`) gets no slot, and its fields stay in
  their variant, allocated as in the core form. Jumps and self calls are
  lowered before every variant is known, so they are put in slots when the
  state machine is emitted.
- **Why:** The core form allocates a variant at every call and jump (104
  to 232 bytes in round 7's LwOutSelf and LwSmPerf). Passing a live value
  in a slot would keep it referenced across the jump, so an array updated
  before the jump was shared and copied at every iteration (probes
  J4Arr/J4For quadratic; Sieve with only `field-order` and
  `state-machines` on: 53 s at its small size; RF-1, 5c5f6fc). A
  placeholder of a type without a finite value stopped the loop with
  "INTERNAL PANIC: unreachable code has been reached" at its first jump,
  hence the guard (round 7 RV7L-03, 69ab202; test `RtJpSlots`).
- **Where:** `Opt/StateMachines.lean`: `slotPlaceholder`,
  `placeholderFiniteE`/`placeholderFiniteB` (the guard), `SlotLayout`,
  `slotLayout`, `smCall`, `emitStateMachineAlongside`,
  `alongsideSelfCall`, `alongsideJumpCall`, `alongsideForm`;
  `runtime/prelude.rr`: `l2r_str_shared_empty`; hook
  `LowerHooks.stateMachine` (`StateMachineHook`), which tags the planned
  form (`StateMachine.form`) so each hook handles its own.
- **Remove only if:** the pass is off (the core form allocates a variant
  per call and jump).
