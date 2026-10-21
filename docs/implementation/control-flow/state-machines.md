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
  off; 3597a31). Reussir has no guaranteed tail calls. The enum is
  shared because Reussir's token reuse gives the matched value's cell to
  the variant of the next call or jump, which then only stores its fields.
  A `[value]` enum (possible since Reussir's old bug 1 is fixed in
  lean2rr's base,
  [../reussir-workarounds/correctness-bugs.md](../reussir-workarounds/correctness-bugs.md#old-bug-1-value-enum-payloads-were-lost-when-moved))
  moves the whole variant at every jump. Measured with `state-machines`
  off (2026-10-19, cachegrind with SVE off, and the allocation counter;
  shared to `[value]`): `RtSmDecode` at size 200000 239.2 to 370.0
  million instructions (its state machine 116.5 to 251.3 million;
  allocations 42,835 to 135), `RtJpSlots` 119.1 to 126.7 million
  (291,440 to 109,621 allocations), `RtStateMachines` 983.5 to 853.9
  million (5,172,954 to 2,504,832 allocations). The default form (next
  entry) allocates nothing either way. The "inlined into it" case was a loop of
  `Std.Http` that stayed mutually recursive (5585f99).
- **Where:** `Lower/StateMachine.lean`: `stateMachinePlan`,
  `hasSelfTailCall`, `outlinedBodies`, `withInlinedJps`,
  `stateMachineSelfCall`, `stateMachineJumpCall`, `emitStateMachine`;
  `Lower/Ctx.lean`: `StateMachine`, `JumpAction.enter`; `Lower/Code.lean`:
  `lowerCode` (the re-entry), `lowerDecl`. Required part
  `loop-state-machines` in `Opt/Registry.lean`.
- **Remove only if:** Reussir guarantees tail calls, or a multi-arm
  `[value]` enum and a mutual tail call both become free.

### A cycle of tail calls between declarations runs in one state machine

- **What:** For declarations that call each other in tail position (a
  strongly connected group, of two or more, of the graph of saturated tail
  calls `let x := g args; return x` between declarations with parameters),
  lean2rr emits one more state machine, `<f>_cyc_sm`, named after the
  first declaration `f` (in lean2rr's internal order of declarations, not
  the order of the source) and planned whatever its join
  points: one entry variant per declaration (the first one's is the entry),
  whose fields are its parameters and whose arm is its lowered code, and one
  entry function per declaration, `<g>_cyc`, which enters at its variant.
  Each declaration also keeps its own function, lowered as if it were
  alone (with its own self-loop state machine where it has one), except
  that its tail calls of the other declarations of the cycle call their
  entry functions. In the state machine, a tail call of a declaration of
  the cycle re-enters it at that declaration's variant (a self tail call
  of the function, a loop). A call that is not a tail call calls the
  callee's own function, from the state machine too. So the state machine
  is entered only by a tail call between two declarations of the cycle,
  and then runs the cycle in one frame. Both forms (the core form and
  `state-machines`' slots) handle the extra entries as they handle
  join-point variants. No state machine: for a group whose declarations
  have different Reussir result types, or one of which has no code of its
  own (`IO.Process.output`'s glue). A tail call of another declaration
  than the one whose code it is (the cycle's first declaration too) stays
  a call of the callee's own function when the caller keeps an argument
  until it returns (`borrowKeeps`; resource programs,
  [../ownership.md](../ownership.md)): natively it is no tail call either,
  as Lean's borrow inference keeps tail calls only for a declaration's
  calls of itself (`InferBorrow.preserveTailCall`). `L2R_DEBUG=1` prints
  each group (`lean2rr: one state machine for a cycle of tail calls:
  ...`).

  ```
  mutual
    def fa (i n : UInt64) : Except String Nat := ... fb (i + 1) n   -- tail call
    def fb (i n : UInt64) : Except String Nat := ... fa (i + 1) n   -- tail call
  end
  ```

  becomes (with `state-machines`) the functions `fa(i, n)` and `fb(i, n)`,
  whose tail calls of each other are `fb_cyc(i + 1, n)` and
  `fa_cyc(i + 1, n)`; one function `fa_cyc_sm(s1 : u64, s2 : u64, m : u8)`,
  whose arm `0` is `fa`'s code and arm `1` is `fb`'s, the tail call of
  `fb` in arm `0` being `fa_cyc_sm(i + 1, n, 1)`; and `fa_cyc(i, n)`,
  `fb_cyc(i, n)`, which call `fa_cyc_sm(i, n, 0)`, `fa_cyc_sm(i, n, 1)`.
- **Why:** Native Lean's C code makes these calls sibling calls (jumps),
  so the cycle runs in constant stack. As separate Reussir functions, the
  calls were sibling calls only where LLVM could make them, and lean2rr's
  own representations kept it from that: a result of several words
  (`flatten-structs`' tuple of `IO Nat`, `IO (Nat × String)` or
  `Except ε α`; not always: `IO Unit` and `Nat × Nat` kept theirs), whose
  returns LLVM merged into one block of phis that its code generator does
  not split again; or a callee that is a state machine with more slots
  than the caller, which needs more stack arguments than the caller
  received.
  Each call then kept its frame: `RtOutlineStates` (two long IO functions
  with outlined join points, a frame of 288 bytes per call) used 273 MB at one
  million calls and overflowed Lean's 1 GiB stack at five million, where
  native Lean uses 8 MB; with `jp-small` off 317 MB at one million. Found
  by the review of `sm-dispatch` (2026-10-21), from dev 101746e5. After:
  6.8 MB at every size. Two small `IO Nat` functions that call each other
  overflowed a 1 MiB stack at a million calls (native: constant stack).
  The declarations keep their own functions for the calls that are not
  tail calls: LLVM sizes the state machine's frame for all its arms, so
  if every call entered it, a deep recursion of a small declaration in a
  cycle with a big one would use the big frame at every level: `walk`
  (non-tail recursion) in a cycle with `heavy` (48 live values, 13
  parameters) about 450 bytes per level instead of about 47, and 100000
  levels would overflow an 8 MiB stack. With its own function, `walk`
  uses 14.5 MB at 100000 levels (native 17.3 MB; `walk`'s frame is 80
  bytes, as its call into the state machine passes 14 arguments, 6 of them
  on the stack on aarch64). A tail call of another declaration (the
  cycle's first declaration too) gets the borrow check: a file handle
  passed owned to a borrowed parameter must stay open until the call
  returns, as natively. Cost: each declaration's code is lowered twice
  (its function and its arm). The CslInitOnly translation has 30 cycles,
  all unreachable (`conv-liveness` drops their functions): its `.rr` grows
  by 5 KB (of 26.9 MB), with 8 more helper functions, and lean2rr's peak
  RSS by 13 MB (of 4.98 GB), against dev 0810b9ec. The shared bench set's
  47 programs and the classic corpus have no such cycle (their `.rr` are
  unchanged). Residual cost: a recursion that is not a tail call but
  passes a tail call between two declarations of the cycle at every level
  (`f` calls `g` not in tail position, `g` tail-calls `f`) enters the
  state machine at every level, and its frame, sized for all its arms, is
  on the stack at every level with `g`'s. When one declaration of the
  cycle is big, that is about 450 bytes per level instead of about 47,
  enough to overflow a small stack where each declaration as a function
  of its own passes: `RtTailCyclesStack2` (`walk2` calls `step2` not in
  tail position, `step2` tail-calls `walk2`, in a cycle with `heavy2`)
  overflows a 1 MiB stack at 5000 levels; at 100000 levels on an 8 MiB
  stack it overflows with a peak RSS of 55.1 MB, where each declaration as
  a function of its own uses 11.3 MB and native Lean 17.2 MB.
  Tests: `RtTailCycles` (`.pipe`: a million calls on a 1 MiB stack:
  multi-word results, a cycle of three, two state machines with different
  slot counts; `.l2r-debug`: the groups; `sm-slots-check.sh`: the slots
  that a call between them passes), `RtOutlineStates` (300000 calls on a
  1 MiB stack), `RtTailCyclesStack` (`walk` and `heavy`: 5000 levels on a
  1 MiB stack), `RtTailCyclesBorrow` (handles passed owned to borrowed
  parameters in a cycle of two and one of three, and in the state
  machine's arms of both declarations of a cycle), `RtTailCyclesStack2`
  (the residual cost, `.xfail`).
- **Status:** the residual cost is accepted for now. Planned fix: a small
  trampoline loop that calls each arm as a function of its own, which
  returns the next step (the step values that `Outline` uses), so that
  the state machine's frame stays small.
- **Where:** `Lower/StateMachine.lean`: `tailCallees`, `tailCallGroups`,
  `stateMachinePlan` (`cycle`: the names `_cyc`), `emitStateMachine`
  (`StateMachine.entryFn`, the entry functions of the other
  declarations); `Lower/Ctx.lean`: `SmMember`, `StateMachine.members`,
  `StateMachine.entryFn`, `CodeCtx.decl`, `CodeCtx.cycle`;
  `Lower/Code.lean`: `tailCallEntry` (re-entry in a state machine, entry
  from a declaration's own function, the borrow check), `DeclSetup`,
  `setupDecl`, `lowerDeclCode`, `lowerDecl` (`cycle?`), `lowerGroup`;
  `Opt/StateMachines.lean`: `emitStateMachineAlongside` (the entry
  functions); `Emit/Program.lean`: the lowering loop. Required part
  `loop-state-machines`.
- **Remove only if:** Reussir guarantees tail calls (a call between
  functions with different parameters then needs no frame).

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
  slot, and its fields stay in their variant: the entry point is then a
  `[value]` enum of the fields without a slot (no heap cell; its other
  variants are nullary, so its values are small).
  Jumps and self calls are
  lowered before every variant is known, so they are put in slots when the
  state machine is emitted.
- **Why:** The core form allocates a variant at every call and jump (104
  to 232 bytes in round 7's LwOutSelf and LwSmPerf), unless token reuse
  gives it the matched variant's cell. Passing a live value
  in a slot would keep it referenced across the jump, so an array updated
  before the jump was shared and copied at every iteration (probes
  J4Arr/J4For quadratic; Sieve with only `field-order` and
  `state-machines` on: 53 s at its small size; RF-1, 5c5f6fc). A
  placeholder without a finite value stopped the loop with "INTERNAL
  PANIC: unreachable code has been reached" at its first jump, hence the
  guard (round 7 RV7L-03, 69ab202; test `RtSmGuard`, whose state
  machine carries a value of a type without a finite value); since round 9
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
  the entry point a `[value]` enum (test `RtSmGuard`; until 2026-10-19 a
  shared enum, because of Reussir's old bug 1).

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
  and after (1985.3: its inflate loop is not threaded in any form: it had
  11 variants, more than DFAJumpThreading threads; since a join point
  declared in an outlined body can be J2 it has 5 and is threaded,
  [join-points.md](join-points.md#a-join-point-declared-in-an-outlined-body-can-be-j2-there)),
  compression (Z01c) 6949.8 to 6924.6 million (6949.8); Cedar (Z06d)
  57793 to 57343 million (57358).
- **Where:** `Opt/StateMachines.lean`: `emitStateMachineAlongside`
  (`scalar`, `modeTy`, the wildcard arm), `smCall` (`SlotLayout.tags`).
  Test: `tests/runtime/sm-slots-check.sh` (with `RtSmDecode`,
  `RtStateMachines`, `RtJpSlots`; `RtSmU32`, a state machine of 261
  variants, whose entry point is a `u32`; `RtSmGuard`, whose entry point
  is a `[value]` enum because a variant keeps a field; `RtTailCycles`,
  state machines of cycles of tail calls; it also checks that
  LLVM threads the loops of RtSmDecode and `RtSmNestedJp`, lean-zip's
  inflate loop in small). `RtSmU32` and `RtSmGuard` turn
  `jp-small` off (`.opts`): it would copy their small join points to the
  jumps, and no state machine would be left.
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
