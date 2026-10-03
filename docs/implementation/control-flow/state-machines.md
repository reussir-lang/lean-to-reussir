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

### State machines entered without allocation (`state-machines`)

- **What:** The optional form passes the declaration's parameters beside a
  nullary entry variant, so calling the declaration and its self tail calls
  allocate nothing. A jump to an outlined join point passes placeholders
  (`zeroValue`) for those parameters, never the parameters themselves:
  the join point's variant already carries every variable its body uses.
- **Why:** Passing the parameters at a jump kept their old values
  referenced across it, so an array updated before the jump was shared and
  copied at every iteration (probes J4Arr/J4For quadratic; Sieve with only
  `field-order` and `state-machines` on: 53 s at its small size; RF-1,
  5c5f6fc).
- **Where:** `Opt/StateMachines.lean`: `emitStateMachineAlongside`,
  `alongsideSelfCall`, `alongsideJumpCall`, `alongsideForm`; hook
  `LowerHooks.stateMachine` (`StateMachineHook`), which tags the planned
  form (`StateMachine.form`) so each hook handles its own.
- **Remove only if:** the pass is off (the core form allocates an entry
  variant per call). **Known defect at b299aab:** a parameter whose type
  has no finite value for its placeholder (`zeroValue` builds
  `l2r_unreachable` inside it, e.g. `inductive W | bad (e : Empty) | ok
  (n : Nat)`) makes the loop stop with "INTERNAL PANIC: unreachable code
  has been reached" at its first jump. Fixed on branch `fix-r7-low` (round
  7 RV7L-03, 69ab202, in progress): every variant nullary, the join
  points' values in parameter slots, and a guard that keeps such a type in
  its variant.
