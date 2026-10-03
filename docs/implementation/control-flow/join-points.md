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
  one nested in the copy, or another one whose own body is small), and
  (3) the copies beyond the first add at most 2000
  (`(jumps - 1) × copySize`).
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
  to 300-350 and stay plain loops.
- **Where:** `Opt/JpSmall.lean`: `isSmallJp`, `codeSize`, `copySize`,
  `copyBudget` (480), `copiesBudget` (2000); hook
  `LowerHooks.duplicateJp`, consulted by both `chooseOutlined` and
  `lowerCode` with the same bodies and jump counts, so they decide alike.
- **Remove only if:** the pass is off (correct; more outlined join points).

### Outlined join points capture what their jumps pass by name

- **What:** An outlined join point (J3, J4) becomes a function of its free
  variables (under the names they have where it is declared) and its
  parameters; every jump passes them under those names. The variables
  captured by the outlined join points in scope are recorded
  (`CodeCtx.captured`), so a join point outlined in an alternative that
  bound a matched variable again (a fresh nullary value, a converted boxed
  scrutinee, a lazily bound field) captures the old names its jumps pass.
  Free variables are also found inside casts (an `RR.Expr.cast` node).
- **Why:** Every `Std.Http` program failed in rrc with "unknown variable"
  (round 6 IO6-14, 8f1dfa7, test `RtJpRebound`); an `IO.FS.Mode` index in
  a join point was missed inside a cast (adv2 EFF-2, aa03809).
- **Where:** `Lower/Code.lean`: `lowerCode` (the `.jp` case),
  `rrFreeVars`; `Lower/Ctx.lean`: `CodeCtx.captured`.
- **Remove only if:** never.

### A local `fun` left after lambda lifting is a raw closure

- **What:** A local function (lambda lifting normally removes them all) is
  lowered defensively to nested `raw` function values.
- **Why:** Stage 2's lambda lifting should leave none; if one slips
  through, the program is still translated, with the closure semantics.
- **Where:** `Lower/Code.lean`: `lowerCode` (the `.fun` case).
- **Remove only if:** never.
