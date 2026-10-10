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

### The entry point of nullary variants is an integer (`state-machines`)

- **What:** When every variant of a state machine is nullary (no field
  without a slot, the usual case), its entry point is an integer, not an
  enum: a `u8` (a `u32` above 256 variants). Variant `i` is the literal
  `i`: `0` is the declaration's own entry, then come the outlined join
  points in their order. The function matches its last parameter on the
  literals `0`, `1`, ..., one arm per variant, and then has a wildcard arm
  `_ => { l2r_unreachable<R>() }` (`R` is its result type), which no call
  reaches. A variant that keeps a field (the soundness guard above) makes
  the entry point a shared enum, as in the core form.

  ```
  fn f_sm(s1 : Nat, s2 : RVec<u8>, m : u8) -> R {
      match m {
          0 => { ... f_sm(x, a, 1) ... },        // the entry
          1 => { ... f_sm(y, s2, 0) ... },       // join point j1
          _ => { l2r_unreachable<R>() }
      }
  }
  ```
- **Why:** A shared enum's nullary variant is a pointer to a static cell.
  The state machine's `match` loaded the tag through it and tested the
  cell's count at every entry: in lean-zip's inflate loop (Z01d) a load, a
  test and a branch at each of its two or three entries per output byte.
  A `[value]` enum (the form before this one) has no pointer, but in LLVM
  it is a struct of its tag and an empty payload. After tail-call
  elimination, the loop then carries its entry point in a phi of that
  struct type, and the `switch` at the loop's head reads a field of the
  phi. LLVM's DFAJumpThreading (in the O3 pipeline that `-O aggressive`
  runs) threads a loop only through a `switch` on a phi (or select) of
  integers, so it did not thread these loops. On an integer it threads them: each jump
  goes directly to the arm that it enters, and only the function's entry
  has the `switch`. Measured in the LLVM IR (blocks `.jtN` of
  DFAJumpThreading), the loops that it now threads are the same loops
  that it threads when it is added at the end of Reussir's pipeline (an
  evaluated Reussir change that is not necessary now), and one more:
  RtSmDecode's decode loop; in lean-zip's driver (Z01c, Z01d) 4 of its 16
  state machines (two greedy lz77 loops, the gzip decoder's loop, the
  split heuristic); in Cedar (Z06d) 24 of 41 (22 specializations of
  protobuf's `parseMessageHelper`, `String.Slice.Pos.skipWhile`,
  `Parsec.manyCharsCore`). Every variant has its own literal arm and the
  wildcard is unreachable, because a wildcard for the last variant makes
  the `switch`'s default reachable: its jump table then has a range check
  at each entry where the loop is not threaded (lean-zip's inflate loop
  `goTreeFreeU` on dickens: 891 to 930 million instructions). LLVM's range
  analysis makes an unreachable wildcard's default unreachable where it
  knows the range (from the literals that the callers pass), so that loop
  is unchanged. Where the entry point comes back through an outlined
  part's step value (`L2RStep_k`, Outline), the range is not known and the
  check stays; such a loop of Z01c (`lz77LazyMergedLoop`) still runs fewer
  instructions than with the enum (415.4 to 407.4 million). Wall time: at the next joint benchmark. Supporting detail
  (callgrind, instructions, against the `[value]` enum; the programs'
  `.rr` of the benchmark set at 0b6ef980 with their entry points changed
  to this form; in parentheses: the `[value]` enum with DFAJumpThreading
  added at the end of Reussir's pipeline): RtSmDecode at size 200000,
  190.5 to 171.3 million (171.3), its decode loop 72.3 to 52.7 million
  (52.7); lean-zip on dickens, decompression (Z01d) 1985.3 million before
  and after (1985.3: its inflate loop is not threaded in any form),
  compression (Z01c) 6949.8 to 6924.6 million (6949.8); Cedar (Z06d)
  57793 to 57343 million (57358).
- **Where:** `Opt/StateMachines.lean`: `emitStateMachineAlongside`
  (`scalar`, `modeTy`, the wildcard arm), `smCall` (`SlotLayout.tags`).
  Test: `tests/runtime/sm-slots-check.sh` (with `RtSmDecode`,
  `RtStateMachines`, `RtJpSlots`; it also checks that LLVM threads
  RtSmDecode's loop).
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
