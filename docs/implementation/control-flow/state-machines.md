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
  checked on every state machine: a type without a finite placeholder
  (`zeroFinite`: a type without a finite value, such as `Empty`) gets no
  slot, and its fields stay in their variant, allocated as in the core
  form. Jumps and self calls are
  lowered before every variant is known, so they are put in slots when the
  state machine is emitted.
- **Why:** The core form allocates a variant at every call and jump (104
  to 232 bytes in round 7's LwOutSelf and LwSmPerf). Passing a live value
  in a slot would keep it referenced across the jump, so an array updated
  before the jump was shared and copied at every iteration (probes
  J4Arr/J4For quadratic; Sieve with only `field-order` and
  `state-machines` on: 53 s at its small size; RF-1, 5c5f6fc). A
  placeholder without a finite value stopped the loop with "INTERNAL
  PANIC: unreachable code has been reached" at its first jump, hence the
  guard (round 7 RV7L-03, 69ab202; test `RtJpSlots`); since round 9
  (RV9C-01) only types without a value have no finite placeholder, and the
  guard asks `zeroValue`'s own search (`zeroFinite`), so the two agree.
- **Where:** `Opt/StateMachines.lean`: `slotPlaceholder?` (the guard,
  over `Lower/Conv.lean`'s `zeroFinite`), `SlotLayout`,
  `slotLayout`, `smCall`, `emitStateMachineAlongside`,
  `alongsideSelfCall`, `alongsideJumpCall`, `alongsideForm`;
  `runtime/prelude.rr`: `l2r_str_shared_empty`; hook
  `LowerHooks.stateMachine` (`StateMachineHook`), which tags the planned
  form (`StateMachine.form`) so each hook handles its own.
- **Remove only if:** the pass is off (the core form allocates a variant
  per call and jump).

### The entry enum of nullary variants is a value enum (`state-machines`)

- **What:** When every variant of a state machine's entry enum is nullary
  (no field without a slot, the usual case), the enum is a `[value]`
  enum: a scalar tag (`i8`), as for Lean's field-less inductives. A
  variant that keeps a field (the soundness guard above) makes the enum
  shared, as in the core form.
- **Why:** A shared enum's nullary variant is a pointer to a static cell.
  The state machine's `match` loaded the tag through it and tested the
  cell's count at every entry, and a re-entry passed the pointer: in
  lean-zip's inflate loop (Z01d) this was a load, a test and a branch at
  each of its two or three entries per output byte. A field-less
  `[value]` enum has no payload, so Reussir bug 1 (lost payload bytes of
  `[value]` enums whose arms differ) cannot apply. Wall time: with the
  next entry (both changes measured together there). Supporting detail
  (callgrind): RtSmDecode's decode loop without its `dbgTraceIfShared`
  calls, 4 rounds at size 1000000, 441 to 392 million instructions.
- **Where:** `Opt/StateMachines.lean`: `emitStateMachineAlongside`
  (`modeVariants`). Test: `tests/runtime/sm-slots-check.sh` (with
  `RtSmDecode`, `RtStateMachines`, `RtJpSlots`).
- **Remove only if:** never (speed only).

### A jump passes on the slots its arm does not bind (`state-machines`)

- **What:** In the arm of variant `u`, a call of the state machine in tail
  position (a self tail call, a jump) passes each slot that the target
  does not fill and that `u` does not bind as the slot itself, not as a
  new placeholder. A slot that `u` binds and the target does not fill
  still gets a placeholder. Elsewhere (a call inside a closure, which the
  lowering does not make) every slot the target does not fill gets a
  placeholder.
- **Why:** Before, every jump rebuilt the placeholder of every slot it
  did not fill, and every arm released the slots it did not bind: per
  iteration a constant per slot and a test per slot of a counted type
  (`Nat`, arrays), and the slots were moved between registers and the
  stack. Sound by induction: when the state machine is entered at a
  variant, each slot that the variant does not bind holds a placeholder
  (the declaration's function passes placeholders; a jump passes
  placeholders or such slots), so passing one on is passing a
  placeholder, never a live value (which would keep an array shared,
  RF-1 above). Wall time with the `[value]` entry enum (median of 9,
  pinned to cores 15-19, 2026-10-09): lean-zip's decompression (Z01d)
  2.058 to 1.853 s, 0.736 to 0.663 of native; its compression (Z01c)
  0.975 to 0.969 of native; RtSmDecode's decode loop without its
  `dbgTraceIfShared` calls (size 16000000) 0.637 to 0.491 s, 0.970 to
  0.748 of native (-23%). Supporting detail (callgrind): that loop 392 to
  272 million instructions (size 1000000); lean-zip's inflate loop (Z01d
  on dickens) 1346 to 1015 million with both changes.
- **Where:** `Opt/StateMachines.lean`: `smCall` (`untouched`),
  `emitStateMachineAlongside` (`untouched`, `place`), `rewriteCallsE`
  (`tail`). Test: `tests/runtime/sm-slots-check.sh`; `RtJpSlots` and
  `RtSmDecode` check that arrays stay unshared (`dbgTraceIfShared`).
- **Remove only if:** never (speed only).
