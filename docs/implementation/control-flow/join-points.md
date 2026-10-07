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
  cannot be J2; it is outlined too unless J1 or J1′ inlines it there.
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

### A J2 join point with several parameters yields a value tuple

- **What:** The structured `let` of a J2 join point with several
  parameters produces a generated `[value]` struct `TupleN` (N a fresh
  number; one struct per list of field types), taken apart
  afterwards.
- **Why:** A Reussir block yields one value; a value struct allocates
  nothing (and is not a multi-arm value enum,
  [Reussir bug 1](../../../reussir-bugs/01-value-enum-payload.md)).
- **Where:** `LowerBase.lean`: `tupleType`; `Lower/Code.lean`:
  `lowerCode`.
- **Remove only if:** never.

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
  `RR.Expr.cast` node).
- **Why:** Every `Std.Http` program failed in rrc with "unknown variable"
  (round 6 IO6-14, 8f1dfa7, test `RtJpRebound`); an `IO.FS.Mode` index in
  a join point was missed inside a cast (adv2 EFF-2, aa03809); a join
  point outlined in an arm that returned a rebuilt value did not capture
  the binder of a converted field (hunt 2026-10-07, test
  `RtFreshRebuildJp`).
- **Where:** `Lower/Code.lean`: `lowerCode` (the `.jp` case),
  `rrFreeVars`; `Lower/Ctx.lean`: `CodeCtx.captured`.
- **Remove only if:** never.

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
