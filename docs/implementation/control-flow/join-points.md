# Join points

Reussir has no join points, so each becomes structured code. Paths are
relative to `lean2rr/LeanToReussir/`. Plan
[§5.6](../../translation-plan.md#56-join-points).

### The strategy: J1, J2, J1′, then J3 (or J4)

- **What:** A join point jumped to once is inlined there (J1). One whose
  scope ends in jumps to it on every path becomes a structured `let`
  computing its arguments, followed by its body (J2). One that is neither
  but small is duplicated at each jump (J1′, optional pass `jp-small`).
  Otherwise it is outlined into a function called in tail position (J3),
  or, in a loop, a variant of a state machine (J4). The choice is a
  fixpoint over the declaration: J2 needs every jump to stay in the same
  Reussir function, so a join point jumped to from inside an outlined body
  cannot be J2 (unless it is declared in that body: next entry); it is
  outlined too unless J1 or J1′ inlines it there.
- **Why:** J3 is the last resort: a self tail call through an outlined
  function makes a loop mutually recursive, and LLVM makes a mutual tail
  call a jump only when it can be a sibling call (a `for` loop overflowed a
  1 GiB stack at 10^7 iterations); and J1/J2 keep "destructure the old
  value" and "build the new one" in one function, which Reussir's token
  reuse needs.
- **Where:** `Lower/JoinPoints.lean`: `chooseOutlined`, `countJumps`,
  `endsInJumps`, `jumpsIn`, `jpBodiesOf`; `Lower/Code.lean`: `lowerCode`
  (the `.jp` and `.jmp` cases); `Lower/Ctx.lean`: `JumpAction`.
- **Remove only if:** never.

### A join point declared in an outlined body can be J2 there

- **What:** For the rule above, only the outlined join points declared in
  the join point's scope count, not the outlined join points around its
  declaration. A join point declared inside the body of an outlined join
  point (J3, or a variant of a state machine, J4), whose scope ends in
  jumps to it on every path, is a structured `let` (J2) in that body.
  Example: the slow path of lean-zip's inflate loop
  (`InflateBuf.goTreeFreeU`) is an outlined join point of the loop's state
  machine. Inside it are the join points of the inlined table lookup (the
  `||` of `if len == 0 || len > cnt`, the value of `let e := if i < size
  then a[i] else 0`) and of the `Except` results of the inlined `takeBits`.
  Each of them was a variant of the state machine (11 variants). Now each
  is a `let` in the slow path's arm (5 variants).
- **Why:** A jump to a join point can only be in its scope, and the scope
  is inside every body that contains the declaration. So the outlined join
  points around the declaration are one function with all its jumps. Only
  an outlined join point declared in the scope can hold a jump from another
  function; the check counts those as before. Each extra variant costs a
  jump through the `switch` at the head of the state machine's loop: the
  moves of the slots and an indirect branch. LLVM's DFAJumpThreading turns
  those jumps into direct ones, but it refuses when cloned/original
  instructions exceed 7.5 (`dfa-max-cloned-rate`, LLVM 23; each state
  clones the loop's head and latch), which for a J4 loop means about 8 or
  more states. The 11-variant inflate loop was not threaded (its `switch`
  had all of the benchmark's indirect mispredicts); the 5-variant one is.
  Measured (cachegrind with branch simulation, SVE off, 2026-10-21, against
  101746e5; instructions, then indirect and conditional mispredicts): the
  inflate loop on dickens (ZipBench `d`), 1148 to 496 million instructions,
  14.3 million mispredicted dispatches to none; Z01t (decompression of the
  Silesia tar, ZipBench) 37.79 to 27.77 billion (native 28.07), 217.8
  million to 189, 128.8 to 119.1 million; Z01d (the same through
  Survey.Main) 33.57 to 23.55 billion (native 25.14), 217.8 million to 199,
  108.3 to 139.2 million; Z01r (round trip at level 9) 129.64 to 127.84
  billion (native 117.87), 50.0 million to 256, 344.4 to 316.9 million;
  Z01c (compression) 149.72 to 151.01 billion (+0.9%; native 125.60), 19296
  before and after, 557.5 to 418.1 million (its `lz77LazyMergedLoop` runs
  3% more instructions: LLVM inlines and threads more of it); Cedar (Z06t,
  Z06g, Z06d) unchanged (-0.003% instructions). Cachegrind's model predicts
  a conditional branch from its address and the last branches in a table of
  16384 counters, so a new code layout alone moves its conditional
  mispredicts: in Cedar by -2% to +12%, also in functions whose code did
  not change (mimalloc's). Only the instructions and the indirect
  mispredicts above are firm. Wall time: at the next joint benchmark. Of
  the bench set's 47 programs, only lean-zip's two drivers and Cedar change
  (the `.rr` of the others is byte-identical); lean-zip's `.rr` is 5.8%
  smaller, and its 19 state machines have 81 match arms instead of 146.
- **Where:** `Lower/JoinPoints.lean`: `chooseOutlined` (`inside`,
  `jumpedFromOutlined`). Test: `RtSmNestedJp` (its state machine has 5
  variants, 10 before), checked by `tests/runtime/sm-slots-check.sh` (at
  most 7 variants, and the loop threaded).
- **Remove only if:** never (the condition is exact).

### A J2 join point with several parameters yields a value tuple

- **What:** The structured `let` of a J2 join point with several
  parameters produces a generated `[value]` struct `TupleN` (N a fresh
  number; one struct per list of parameter types, `tupleType`), taken
  apart afterwards. Its fields are the parameters in decreasing alignment,
  ties in parameter order (`memberOrder`, the order of every generated
  tuple and of records with `field-order`,
  [records](../representations/records.md#fields-are-ordered-by-decreasing-alignment)):
  a jump builds the tuple in that order, and the join point reads
  parameter `i` from its field. Example: the join point of `'a' ≤ c && c ≤
  'z'` in a fold that carries a `Nat` takes `(b : Bool) (n : Nat)`
  (parameters in the order of their first use, `stableJpParams`); its
  tuple is `Tuple(Nat, bool)`, not `Tuple(bool, Nat)`.
- **Why:** A Reussir block yields one value; a value struct allocates
  nothing. The order: with the driver's `--no-pack-record-members`,
  Reussir lays a member that the next member's alignment pads out as a
  wider integer (a `bool` before a `Nat`: an `i64`) and stores only the
  field's own type in it (`store i1`). LLVM then cannot take the struct
  apart: the `bool` goes through a stack slot, and conditions on it are no
  longer folded (Strings' `charStats` loop with `Tuple(bool, Nat)`: the
  whole program ran 3.0% more instructions; issue 17 of `reussir-bugs/`).
  Without padding between members there is no widened member.
- **Where:** `LowerBase.lean`: `tupleType`, `memberOrder`,
  `positionsOf`; `Lower/Code.lean`: `lowerCode` (`.jp`, `.jmp`);
  `Lower/Ctx.lean`: `JumpAction.yield`.
- **Remove only if:** never (the tuple); the order only if Reussir no
  longer widens a padded member (issue 17) or the driver packs record
  members again.

### Join points are sunk before the choice (`jp-sink`)

- **What:** Before choosing, every join point is moved down to the
  smallest part of its scope containing all its jumps: past `let`s, into
  the single `cases` branch that jumps to it, into the body or continuation
  of another join point. Binders are unique, so free variables stay in
  scope, and no code is duplicated.
- **Why:** A join point declared before a `cases` of which one branch uses
  it is then often J2 instead of outlined; loops stay self-recursive
  (9346467).
- **Where:** `Opt/JpSink.lean`: `sinkJoinPoints`, `sinkInto`,
  `hasJumpTo`; hook `LowerHooks.prepareBody`.
- **Remove only if:** the pass is off (correct; more outlined join points
  and state machines).

### Small join points are duplicated, within three bounds (`jp-small`)

- **What:** A join point that is neither J1 nor J2 is duplicated at its
  jumps when (1) its own body is at most 40 bindings, alternatives and
  exits (nested join points included), (2) a copy expands to at most 480
  (`copySize`: at each jump, the body of a join point inlined there too:
  one nested in the copy, one jumped to once, whatever its size, or
  another one whose own body is small), and (3) the copies beyond the
  first add at most 2000 (`(jumps - 1) × copySize`), or 4000 for a loop's
  continuation: a join point whose own body (nested join points included,
  not those it jumps to) tail-calls a declaration of the declaration's
  call cycle (`tailCallsInto`).
- **Why:** Outlining puts a function boundary on the path: a loop through
  it becomes a state machine or mutually recursive, and cell reuse cannot
  cross it (a for-loop with `continue`: 7x slower than native before
  duplication, 3f59239; strings 2.15x → ~1.16x with the 40 bound,
  6b0ccbb). Each later bound fixes a blow-up the earlier ones allowed:
  sibling join points jumped to from two others doubled at each step (20
  `match`es on a state: out of memory; 5585f99, test `RtJpChain`); bounding
  the whole closure by 40 turned ordinary loops with `&&`/`||` conditions
  into state machines, 5-9x native (round 6 RV6J-01; JpMut2 overflowed the
  stack, RV6J-02; 38dc337); an 800-arm `match` copied the next `match`'s
  alternatives into every arm (11.7 MB of `.rr`, rrc out of memory; round 6
  RV6J-03, 3dcbdeb, test `RtJpWide`). Loops with compound conditions expand
  to 300-350 and stay plain loops. Round 8 (rv8/lfix): a single-jump join
  point over 40 counted as one node was copied with every copy of its
  jumper, since J1 inlines it whatever its size (jp-sink off: 200 copies,
  4.15 MB of `.rr`, rrc at 12 GB; RV8L-03, 92c5b6a); the 2000 budget
  outlined a loop's continuation after a 60-arm `match`, making the loop a
  state machine or, in mutual recursion, a stack frame more per iteration
  (overflow at 6M; RV8L-04, b7e2a15); 4000 for every join point let
  state-matching functions add 0.5-0.75 MB of `.rr` each (RV8L-05,
  912872d, which restricted it to copies tail-calling the call cycle); and
  a tail call anywhere in the copy, through the join points it jumps to,
  made a whole `match` chain loop continuations from one guarded self
  call (7.26 MB, a 378 s build; RV8L-08, 528a352: own body only).
- **Where:** `Opt/JpSmall.lean`: `isSmallJp`, `codeSize`, `copySize`,
  `tailCallsInto`, `copyBudget` (480), `copiesBudget` (2000),
  `loopCopiesBudget` (4000); `Lower/JoinPoints.lean`: `JpScope` (`bodies`,
  `single`, `loop`); `Pipeline.lean`: `callCycles` (the program's
  direct-call cycles, `LowerCtx.callCycles`); hook
  `LowerHooks.duplicateJp`, consulted by both `chooseOutlined` and
  `lowerCode` with the same scope and jump counts (`CodeCtx.jpSingle`,
  `CodeCtx.loop` in the lowering), so they decide alike.
- **Remove only if:** the pass is off (correct; more outlined join points).

### Outlined join points capture what their jumps pass by name

- **What:** An outlined join point (J3, J4) becomes a function of its free
  variables (under the names they have where it is declared) and its
  parameters; every jump passes them under those names. The variables
  captured by the outlined join points in scope are recorded
  (`CodeCtx.captured`), so a join point outlined in an alternative that
  bound a matched variable again (a fresh nullary value, a converted boxed
  scrutinee, a lazily bound field) captures the old names its jumps pass.
  The binders that a rebuilt matched value reads (`fresh-rebuild`) are
  recorded there too. Free variables are also found inside casts (an
  `RR.Expr.cast` node). The captured variables come in the order of their
  first use in the lowered body (`rrFreeVarsInOrder`), not in the order of
  their names.
- **Why:** Every `Std.Http` program failed in rrc with "unknown variable"
  (round 6 IO6-14, 8f1dfa7, test `RtJpRebound`); an `IO.FS.Mode` index in
  a join point was missed inside a cast (adv2 EFF-2, aa03809); a join
  point outlined in an arm that returned a rebuilt value did not capture
  the binder of a converted field (hunt 2026-10-07, test
  `RtFreshRebuildJp`). lean2rr numbers names with one counter for the
  whole program, so an order by name changed when an unrelated definition
  was added: the outlined function's parameters, a state machine's slots
  (determinism check: RtSmDecode, RtStateMachines, RtJpSlots).
- **Where:** `Lower/Code.lean`: `lowerCode` (the `.jp` case),
  `rrFoldFree`, `rrFreeVars`, `rrFreeVarsInOrder`; `Lower/Ctx.lean`:
  `CodeCtx.captured`. Stage 2 gives the parameters of a join point in the
  order of their first use too
  ([../types/lean-passes.md](../types/lean-passes.md#join-point-parameters-are-put-in-the-order-of-their-first-use)).
- **Remove only if:** never.

### An outlined join point with many calls in one function stays a function

- **What:** An outlined join point (J3) is a function, and rrc's MLIR
  inliner inlines a function of at most 256 operations at every call.
  When one function calls outlined join points so often that their
  copies would add more than 4000 operations to it (Σ (calls - 1) × size,
  over the callees of more than 32 operations), lean2rr marks the join
  points that add the most `#[transform_anchor]`, until the rest is under
  4000, and the inliner leaves them out of line. The rule is not specific
  to join points: it applies to every generated function (required
  practice `inline-anchors`).
- **Why:** `jp-small` outlines a join point whose copies would be too much
  code, and the inliner then copied it back into every jump. `RtJpWide`
  (one `match` with 800 arms, three outlined
  join points of about 160 operations, about 266 calls each) took 740 s
  to build, because LLVM's passes are superlinear in the size of the one
  function that got all the copies; with the join points out of line,
  5 s. Under `leanrt` that `match` is a chain of tests that
  `Outline` cuts into functions of a few arms each, so no function calls
  a join point more than 3 times and nothing is marked.
- **Where:** `Emit/CopyAnchors.lean`; the entry in
  [../reussir-workarounds/build-time.md](../reussir-workarounds/build-time.md#current-cost-the-inliner-copies-a-callee-into-every-call-of-one-function).
  Tests: `tests/runtime/inline-anchors-check.sh` (`RtJpWide`;
  `RtJpAnchors`: a small join point with 300 calls and a larger one with
  4 calls, neither marked; `RtCopyAnchors`: functions, not join points).
- **Remove only if:** rrc's inliner bounds the code that its copies of a
  callee add to one function.

### A local `fun` left after lambda lifting is a raw closure

- **What:** A local function (lambda lifting normally removes them all) is
  lowered defensively to nested `raw` function values: one closure per
  domain of its type at run time (rule 4: none for a phantom domain; a
  closure that ignores its argument at a unit domain for an erased
  parameter that the function does not take, `keepMask`).
- **Why:** Stage 2's lambda lifting should leave none; if one slips
  through, the program is still translated, with the closure semantics.
- **Where:** `Lower/Code.lean`: `lowerCode` (the `.fun` case).
- **Remove only if:** never.
