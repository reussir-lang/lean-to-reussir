# Ownership and runtime glue

Reussir does all reference counting and reuse (Perceus); lean2rr adds none
of its own, except where Lean's *timing* of a release is observable or
where the runtime's containers must cooperate with Reussir's drop glue.
Paths: `lean2rr/LeanToReussir/` for lean2rr's files, `runtime/` for the
runtime.

### Borrowed parameters are emulated for resources

- **What:** Only in a program that creates resources (files, temporary
  files, child processes, promises), lean2rr runs Lean's own borrow
  inference on copies of its declarations and keeps an owned argument that
  may hold a
  resource, passed to a borrowed parameter, alive until the call returns
  (`l2r_release_after`); arguments the caller only borrows itself are left
  alone, so loops keep their tail calls, and function values go through
  `<fn>_boxed` variants. Whether an argument may hold a resource is decided
  for the borrowed parameter it is passed to (`keepsAt`): in a program
  that does not cast, by the whole-program flow analysis that guards
  `flatten-structs` (`Opt/ResourceFlow.lean`), run again on the declarations
  that are lowered (`Emit/Program.lean`, `LowerCtx.resourceHeld?`); in a
  program that casts, which the analysis cannot follow, by the mono type of
  the parameter (`mayHoldRelease`: an `lcAny`, a handle, a function type, a
  thunk or a task, or an inductive, array or reference with such a field at
  its type arguments), not by its Reussir type: with one type per
  inductive, a `List Nat` holds `Box`es, as a list of handles does. Both
  look into closures, thunks and tasks, which may have captured a handle:
  an `IO.FS.Stream` over a file in a record whose other fields a helper
  reads, a `Thunk IO.FS.Handle` that a helper reads with `Thunk.get` (which
  borrows), a task holding a handle that a helper only asks
  `IO.hasFinished` about. Natively calling a closure makes Lean's inference
  take the parameter owned (unless it is marked `@&`), so a borrowed one is
  a value the callee passes on to borrowed parameters, ignores, or reads
  other fields of. Lean takes every parameter of an exported declaration
  (`@[export]`, and `main`) owned, and decides that by name (`isExport`):
  the instances of such a declaration (`helper._l2r_0`) are marked exported
  in the copy of the environment that the inference uses. The rules are in
  plan §5.8, "Borrowing". The inference runs on lean2rr's code after the
  optional passes, so a pass that changes code keeps Lean's code where a
  value may hold a resource: `flatten-structs` leaves alone each
  declaration with a parameter or a result that may hold one, and each
  declaration whose borrow flags decide the flag of such a parameter (a
  callee that gets a field of it), and keeps whole each join point
  parameter that may hold one; the same analysis decides which (by type,
  with closures, thunks and tasks counted, in a program that casts;
  [optional-passes.md](optional-passes.md#structure-arguments-and-results-are-spread-into-their-fields-flatten-structs)).
  So where an argument is kept, the inference saw Lean's code and infers
  what native Lean infers. That rests on the two runs of the analysis
  agreeing (flatten-structs' on its input, the lowering's on its output):
  every parameter that the second run finds holding a resource belongs to
  a declaration that `flatten-structs` left alone. `keepsAt` checks it: a
  kept parameter of a declaration that the pass rewrote (a worker, a
  wrapper, a declaration whose code it changed: `flattenRewritten`, set by
  `Flatten.run`) is an internal error. `keepsAt` is only asked about
  callees with borrow flags, which the inference computed on the lowered
  declarations, the ones the analysis ran on, so its type-rule fallback
  for a declaration the analysis did not see cannot fire (kept as a safe
  default). Elsewhere lean2rr's code can differ (a structure
  that `flatten-structs` split no longer has its constructor), and the
  inference can take borrowed a parameter that native Lean takes owned;
  the argument is then not kept, which nobody can tell: it holds no
  resource.
- **Why:** The rule by type looked at any parameter that the inference
  took borrowed. A cycle of tail calls that passes a new value to a
  parameter the callee stores in a structure (natively owned: a
  constructor's argument, so a tail call) whose reader `flatten-structs`
  splits kept the value until the call returned, so each call stayed a
  call, and 10^6 steps overflowed an 8 MB stack where native runs: with an
  `lcAny` value since the rule existed, with a closure, a thunk or a task
  once the rule counted them (review of the change for closures, test
  `RtBorrowCycleFlatten`). Before that change the type rule did not look
  into closures, thunks and tasks at all, and such a value was released at
  its last use inside the callee: a helper read `T1` from its file where
  native reads `1` (judge 2026-10-27, tests `RtBorrowClosure`,
  `RtBorrowClosureCast`). A cycle of tail calls that passes a new thunk,
  which holds no resource, to a parameter Lean borrows stays a state
  machine, where natively the caller's release after each call makes it
  recurse: the same results with less stack (test `RtBorrowThunkCycle`).
  Natively the caller releases a borrowed argument after the
  call; Reussir releases at the last use, inside the callee. Only resources
  can tell: a handle written by a helper that then reads the file again
  (natively still buffered), a child's stdin pipe a helper writes and then
  waits on (natively no end of file yet) (3f72016, test `RtBorrowRelease`).
  A promise can tell too: its last reference resolves its `result?` task
  with `none`, so a helper that asks `IO.hasFinished` after its last use
  of a borrowed promise got `true`, natively `false` (hunt3 own, test
  `RtBorrowPromise`). The instances of an exported declaration have other
  names than the declaration: their parameters were inferred borrowed, so
  a handle written in an exported helper stayed open until the call
  returned, where natively the helper's last use closes it (hunt3 own,
  test `RtBorrowExport`). An element read with `a[i]!`
  (`Array.get!Internal α inst a i`) derives from the array and from the
  `Inhabited` instance (its value out of bounds): it is borrowed only when
  both are, as in Lean's `explicitRc`. `borrowedVars` read argument 1 (the
  instance) as the array: with an instance parameter and an array of the
  function's own, the element was not kept and closed inside the callee
  (hunt3 own, test `RtBorrowGetBang`); with the array alone checked, an
  instance the function builds (`⟨some h⟩`) was not kept either (review,
  test `RtBorrowGetBangDflt`). Values that Lean's inference does not make
  owned and after which its `explicitRc` puts no `dec` are borrowed too:
  the value of a constant (a closed term such as `#[]`, Lean's
  `fap c #[]`), a constructor applied to no variable (it holds nothing:
  `none`, a scalar natively, or one whose relevant fields are all `◾`), and a join point's parameter to which every jump passes such
  a value or `◾`. Kept, they broke self tail calls that passed them to a
  borrowed parameter, and loops of 10^6 steps overflowed an 8 MB stack
  (hunt3 own and its review, tests `RtBorrowTailConst`,
  `RtBorrowTailNone`, `RtBorrowTailNoneH`).
- **Where:** `Lower/Borrow.lean`: `resourceExterns`,
  `programMakesResources`, `inferBorrowedParams`, `borrowedVars`,
  `borrowInfo`, `keepsAt`, `mayHoldAt`, `flattenRewritten`,
  `mayHoldRelease` (memoized for the run,
  `releaseTypeCache`:
  [translator.md](translator.md#questions-about-types-are-answered-once-per-run)),
  `borrowKeeps`, `releaseAfter`,
  `boxedTarget`; `Emit/Program.lean` (the flow analysis on the lowered
  declarations, `LowerCtx.resourceHeld?`); `Opt/ResourceFlow.lean`:
  `runNoCasts`; `Opt/Flatten.lean`: `run` (sets `flattenRewritten`);
  `Lower/Values.lean`: `lowerConstApp`;
  `runtime/prelude.rr`: `l2r_release_after`; plan
  [§5.8](../translation-plan.md#58-externs-and-runtime-calls)
  ("Borrowing").
- **Remove only if:** Reussir gets borrowed parameters. Limits: a pure
  task that holds no resource is not kept for a borrowed parameter (kept
  only in a program that makes resources and casts, by type), so a pure
  task that no worker has started is deleted at the value's last use
  inside the callee, where natively the caller's release after the call
  can come after a worker started it (plan §10, "Release time of pure
  tasks", test `RtTaskDropReleaseTime`); and the inference runs on lean2rr's
  instances (plan
  [§10](../translation-plan.md#10-known-divergences-and-unsupported-features),
  "Release time of borrowed parameters"). `IO.Promise.isResolved` is
  replaced for the same reason
  ([externs-ffi/shim.md](externs-ffi/shim.md#iopromiseisresolved-is-replaced-borrow-dependent-behaviour)).

### Lent arguments are released last first, by first occurrence

- **What:** After a call, the kept arguments (`borrowKeeps`) are released
  in the reverse order of their first occurrence among the call's
  arguments: `put3 a b c` releases `c`, `b`, `a`; `put4 w h1 h2 h1`
  releases `h2`, `h1`, `w`; in `own3 x y x` with the first parameter owned,
  `x` counts from its first (owned) position, so `y` goes first. A variable
  is kept when it is passed to a borrowed parameter at any position and
  the first such parameter may hold a resource (`keepsAt`; in `own3 x y x`
  the third parameter, not the first). The `_boxed` wrappers (`boxedTarget`) release last
  parameter first.
- **Why:** Lean's `ExplicitRC.addDecAfterFullApp` visits the arguments in
  order, takes each variable at its first occurrence (`isFirstOcc`) when
  some occurrence is borrowed (`isBorrowParam`), and *prepends* its `dec`
  to the code after the call, so the `dec`s run last first; `_boxed`
  functions go through the same pass. Handles show the order: each closes
  and flushes its buffer when released, so several handles on one file
  write their texts last first natively (`CBA`). lean2rr released them in
  argument order (`ABC`), and by first *borrowed* occurrence (cross-test
  XT-1, fixtures A545, A612, A613, A621; test
  `RtBorrowReleaseOrder`).
- **Where:** `Lower/Borrow.lean`: `borrowKeeps` (first occurrences, in
  order), `releaseAfter` (reverses them), `boxedTarget`; plan
  [§5.8](../translation-plan.md#58-externs-and-runtime-calls)
  ("Borrowing").
- **Remove only if:** the borrow emulation goes (see above).

### Values that die at the start of an arm are released newest first

- **What:** In a program that makes resources, when two or more values
  that may hold a resource (by the rule of the borrow emulation,
  `mayHoldAt`: in a program that does not cast, the flow analysis, which
  follows closures, thunks and tasks, so one of them counts only when it
  may have captured a resource; in a program that casts, the type rule,
  where every closure, thunk and task counts) die at the start of a branch
  (the arm of a `match`, a branch of an `if`: values another branch uses
  and this one does not, which the code after it does not use), lean2rr
  releases them there itself with `l2r_release_after`, newest binding
  first. The scrutinee `s` of a `match`, when it may hold a resource and
  dies in the match: in an arm that reads none of its fields it goes with
  the others, first in a constructor's arm and by its own binding in the
  default arm (`_`); in an arm that reads a field (a scalar field too) it
  goes after the others, when a field the arm does not read may hold a
  resource (the same rule). In branches nested in a constructor's arm, `s`
  counts as bound at the `match`. Examples (test `RtDropArmOrder`): two
  handles that die at a branch start close `21`, three `321`; two
  unresolved promises run their `sync` printers `p2` then `p1`; a
  scrutinee holding a handle `S` in a field the arm does not read, the arm
  reading its `Nat` (or `UInt64`) field, with two other handles, closes
  `21S` (`1S` with one); an arm that reads no field `S21`; a default arm
  on such a scrutinee bound first `21S`; a loop's exit `N1N2` for its
  parameters `a = N2`, `b = N1`; a field converted to its own type `BA`; a
  closure holding handle `C`, bound before the scrutinee, `1CS` in an arm
  that reads a field and `SC1b` in one that does not.
- **How:** a step of the core over the generated functions, right after
  `Outline` and before the optional passes over them
  (`LoweredProgram.armRelease`, in `Main.lean`). It computes Reussir's
  liveness on the generated code (free variables, and the rules of
  Reussir's `ownership.rs` for `If`, `Match` and argument lists: what dies
  at an arm's start is what the other arms use, this one does not and
  the code after does not), keeps the recorded values, and orders them by
  their Lean variables' binding order. The lowering records them: before
  the declarations are lowered, `armReleaseVars` numbers every binder of
  each declaration in binding order (`armBinders`: a `let` where it is
  bound, the fields of a `cases` at its alternative's start in field
  order, a join point's parameters after its continuation, since lean2rr
  can copy the body to a jump there) and keeps those that may hold a
  resource (`mayHoldAt`: the flow analysis' answer for the binder,
  `LowerCtx.resourceHeld?`, in a program that does not cast, which knows
  every binder of the lowered declarations; the type rule `mayHoldRelease`,
  `mayHoldResource` with closures, thunks and tasks counted, in one that
  casts) and that are not lent
  (`borrowInfo`: whoever lent them releases them). The numbers and the
  lent variables are kept by declaration and variable, as the flow
  analysis keys its binders, and read with the declaration being lowered
  (`CodeCtx.decl`): a pass can copy a declaration's code without new
  variables (`Opt/SplitMapLoops.lean`'s typed instances of a `map` loop
  keep the loop's); by variable alone, one copy's numbers would replace
  the other's and a variable lent in one copy would count as lent in both
  (bug hunt hunt-resflow, C2; no program showed it). Every lookup of such a
  variable records the Reussir name it gives, with the variable's order
  (`noteVarUse`), so the names lean2rr gives a variable later (a field
  converted to its own type, a field `lazy-fields` binds where it is
  used, a join point's parameter at an inlined jump, a state machine's
  slot bound again) keep its place; and each `match` arm on such a value
  records which binders may hold a resource (`noteArmFields`, the same
  rule). A
  release is an ordinary consuming use, so Reussir adds no release of
  its own: no double release. Once the step releases a scrutinee in one
  arm, Reussir borrows it for the whole `match` and releases it, with the
  other values, oldest first in every arm that does not use it; so then
  the step orders it in every arm where it dies with another recorded
  value (the values it does not record hold nothing whose release shows,
  or someone else holds them). `sink-proj`, after it, moves a
  structure's projection into the branches that use the projected value,
  and counts a release as such a use (the projection comes first, then
  the releases in their order).
- **Why:** Natively `ExplicitRC.addPrologForAlt` releases the values that
  die at an alternative's start in one prolog, sorted by their binding
  index, each `dec` prepended: newest first; `withCtorAlt` gives the
  `cases`'s scrutinee a new index in a constructor's alternative (the
  newest so far), not in the default one; a scrutinee whose fields the
  alternative reads is live until its last projection, so its `dec` comes
  after the prolog. A `cases` with one alternative left (`simpCase`; a
  structure's) is no `cases` and gives no new index. Reussir releases the
  values that die at an arm's start oldest first, and a matched value
  that dies in the match first, after retaining the fields the arm reads.
  Only resources can tell: handles close and flush in that order, and an
  unresolved promise's last reference resolves its `result?` with `none`,
  which runs its `sync` dependents. Through lean2rr the shapes above gave
  `12`, `123`, `p1` first, `S12` (`S1`), `S12`, `S12` and `N2N1`
  (bug hunt hunt-front b2 to b4 and its judge, ArmEdge; test
  `RtDropArmOrder`). A first version ordered a scrutinee by its own
  binding in a branch nested in a constructor's arm: `S1` natively, `1S`
  through lean2rr (Reussir's oldest first had matched there by chance);
  a structure keeps its binding (`2S1`, both in the test). Its review
  found three more shapes where ordering by the Reussir names' numbers
  (lean2rr's one counter) went wrong where Reussir alone had matched: a
  field converted to its own type got a name after the arm's other
  binders (`AB`, natively `BA`); a field that `lazy-fields` binds where it
  is used got a name after the arm's `let`s (`S2`, natively `2S`); and a
  closure holding a handle was not recorded, so in an arm where the step
  had made Reussir borrow the scrutinee, Reussir released the closure
  first (`CS1b`, natively `SC1b`). Hence the order by Lean variable and
  the closures, thunks and tasks among the recorded values (all in the
  test). They were first recorded by type, every closure, thunk and task
  whatever it held; the order of a value that holds no resource does not
  show (but for a pure task, below), and the extra releases changed hot
  code: in the regex benchmarks' VM step (`eachStepChar.go`) the release
  of a closure in the exit arm kept a projection (`let x = s.4`) above
  the match on every step, where `sink-proj` had moved it into the arms,
  and the backtracker's `pushNext` got two releases in its `_` arm
  (review of the regex benchmarks' code after timing run 17). Since then
  the recorded set follows the rule of the borrow emulation.
- **Where:** `Emit/ArmRelease.lean` (`goBlock`, `goMatch`, `Pos`,
  `Info.key`, `LoweredProgram.armRelease`); `Lower/Borrow.lean`:
  `armReleaseVars`, `armBinders`, `mayHoldAt`, `mayHoldRelease`,
  `noteArmFields`;
  `LowerBase.lean`: `noteVarUse`, `LowerState.armVars`, `armNames`,
  `armFields`; the lookups in `Lower/Decls.lean` (`lowerArg`,
  `applyChain`), `Lower/Values.lean`, `Lower/Code.lean` (`return`,
  `lowerCases`), `Opt/LazyFields.lean`; `Emit/Program.lean`
  (`lowerProgram`); `runtime/prelude.rr`: `l2r_release_after`; plan
  [§5.8](../translation-plan.md#58-externs-and-runtime-calls)
  ("Release order at the start of a branch") and
  [§10](../translation-plan.md#10-known-divergences-and-unsupported-features).
- **Remove only if:** Reussir releases the values that die at an arm's
  start newest first and a matched value whose fields the arm reads after
  them (Lean's order). Limits (plan §10, "Release order at the start of a
  branch"): natively Lean's `pushProj` moves the projections at an
  alternative's start into the branches of a `cases` that follows at
  once, so the scrutinee dies at the start of the branches that read no
  field and after the projection in the others, where lean2rr releases it
  at the arm's start (test `RtDropArmPushProj`, with expectation files);
  a `cases` whose alternatives `simpCase` folds into a default
  alternative only after `toImpure` keeps its scrutinee's index there; a
  join point's body that lean2rr places under a `match` (J1, J1′) counts
  the scrutinee as bound there, natively its index at the join point;
  natively the scrutinee and the first field projected in a constructor's
  alternative have one index, so their order when both die at a nested
  branch's start is not specified (lean2rr: the field first). In a
  program that does not cast, a pure task that holds no resource is not
  recorded, so where it dies at an arm's start with other values its
  release keeps Reussir's place (its release time is lean2rr's anyway:
  plan §10, "Release time of pure tasks"). A
  structure that `flatten-structs` splits into its fields holds nothing
  whose release shows (the flow analysis follows closures, thunks and
  tasks, and so does the type rule of a program that casts,
  `mayHoldRelease`), so releasing it field by field shows nothing.

### Reference sets store the new value before releasing the old one

- **What:** `l2r_rc_set_ref` (references) reads the old value, stores the
  new one with Reussir's `cell::set`, and releases the old one and then
  the reference through `l2r_release_value_then`, an FFI call Reussir
  keeps after the store. The reference (the `L2RRefN` record) is passed
  beside its cell: natively the set borrows it and the caller releases it
  after the set, so when the set is its last use the old value goes
  first, then the reference, which frees the new value.
  `l2r_lcell_set` (thunk, task and promise cells) does the same in Rust.
  Both release with `leanrt::drop::release`, as `lean_dec`: a shared
  runtime value (or a box's immediate) is only decremented, in line; a
  record is released inside a free the runtime starts (`drop::free_unique`:
  the record is one pending cell on leanrt's own stack, see
  [below](#a-record-is-released-as-one-pending-cell); one call,
  `free_deferred_call`, so that the texture stays small enough for LLVM to
  inline it into the program's loops, `wait-inline-check.sh`). If it is freed,
  Reussir's glue visits its members first field first, every runtime
  object it reaches there is pushed, and the pops release them last field
  first. The `sync` dependents of the promises it drops run when that
  free ends, before the caller goes on. Other values are dropped (the runtime's
  containers free themselves that way). A reference's cell holds a `Box`,
  which always crosses the FFI boundary.
- **Why:** As `lean_st_ref_set`: code the release runs (the `sync`
  dependents of a promise it drops) must see the new value. Reussir's
  `cell::set` and Rust's assignment release first (round 7 RV7C-01,
  d5169c4). Releasing through the record's `_ffi_release` let Reussir's
  glue free the old value first field first: the dependents of the
  promises it held ran, and the file handles it held were closed, in the
  reverse of native's order (round 8 RV8T-02); and without a hook at the
  end of that free (then Reussir's drain-end hook, now leanrt's own
  `pending::drain`) the end was not seen, so the
  dependents ran late and a condition-variable loop reading its flag first
  waited forever (RV8T-01;
  both 8af8f1a; tests `RtRefSetOrder`, `RtRefSetFiles`,
  `RtSyncLostWakeLoop`, `RtPromiseFreeGlue`). With only the cell passed,
  the cell's last use was the store: when the set was the reference's
  last use, Reussir freed the cell, and the new value with it, before the
  old value (a structure of two handles closed "new.b new.a old.b old.a",
  natively "old.b old.a new.b new.a": test `RtRefSetLastUse`).
- **Where:** `runtime/prelude.rr`: `l2r_rc_set_ref`, `l2r_release_value_then`,
  `l2r_lcell_set` (`l2r_ref_set` too, but `LRef` is no longer used);
  `runtime/leanrt/src/drop.rs`: `release`, `ReleaseValue`,
  `free_unique`, `free_deferred_call`, `free_deferred`, `release_record`;
  `runtime/leanrt/src/pending.rs`: `defer_cell`, `drain`;
  `Lower/Externs.lean`: `refCellOpPlain`.
- **Remove only if:** the `l2r_release_value_then` detour in
  `l2r_rc_set_ref` can go if Reussir's `cell::set` stores before it
  releases and frees in Lean's order, and the reference is released after
  the set; the order inside `l2r_lcell_set` (plain Rust) must stay.

### Runtime objects free through leanrt's pending stack, in Lean's order

- **What:** one stack of pending releases per thread, which Reussir's
  drop glue and leanrt share: Reussir's drop stack (reussir-rt's
  `drop_stack`, with local patches 23-k to 23-m: runs of cells with one
  release function, steps, depth, the end work), which leanrt uses
  through `pending`; and one flag that tells whether a drain runs
  (`pending::releasing`, which `drop::active` wraps). leanrt's releases
  that go through it: the last reference of a
  container (`RVec`, `LRef`: `leanrt::drop::Vec`, the runtime's one-block
  array; `LCell`: `leanrt::drop::Cell`, a transparent wrapper of
  Reussir's `Rc`), of a box's program payload (`any::release_last`), and
  of a record that a reference's or cell's set gives up (`drop::release`).
  Reussir's glue defers there the dead children of the records it frees
  as a worklist (below).
  - The first such release on a thread that finds the flag clear is the
    outermost free. It sets the flag, runs the release, pops the stack
    last pushed first until it is empty, and clears the flag
    (`pending::drain`; a drain of Reussir's glue the same way). Then it
    runs the end work, if a release asked for it
    (`pending::want_end_work`): the promise resolutions put off, then
    lean-runtime's `after_drain` (`task::drained`, registered as the
    stack's end function).
  - A release that leanrt reaches while the flag is set is pushed
    (`drop::defer`, `drop::run`, `pending::defer_cell`). That includes
    every runtime object that Reussir's drop glue reaches (the opaque
    type's drop hook) while it frees a record inside a drain, leanrt's or
    its own, and a stream handle's close and a promise's drop. Outside a
    drain, those two run at once: the close, then `after_drain`
    ([tasks/scheduler.md](tasks/scheduler.md#the-end-of-a-handles-free-waits-for-its-writer-lean-runtimes-drain-end-hook));
    the promise's resolution with `none`
    ([tasks/dependents.md](tasks/dependents.md#no-context-is-ever-suspended-inside-a-free)).
  - Reussir frees records itself, at a bounded stack depth, through that
    stack (Reussir base l2r-base12 and local patches 23-a to 23-p,
    [Reussir issue 23](../../reussir-bugs/23-worklist-drops.md)). A record
    whose last managed member is its one recursive member (a list) is
    freed in a loop. A record type whose drop could recurse otherwise
    (two recursive members, or a managed member after the recursive one:
    the Worklist kind) is freed by a walk under the stack's drain: the
    members in field order, at once, except a member box of a Worklist
    record whose count reaches zero, which is pushed and popped later,
    last pushed first; the last dead child of a cell goes on at once, as
    the drain would pop it next (order (a), the owner's choice). A drop
    that starts while the thread drains only pushes, and the running
    drain frees it. When user code drops a Worklist record, the record's
    own members go in field order, and each dead Worklist child is a drain
    of its own that ends before the next member.
  - So one drain pops the glue's records and leanrt's cells and steps in
    one order, last pushed first, and no Lean code runs inside any drain
    (the end work comes after the outermost one). On l2r-base9 without
    23-k to 23-m the two stacks were separate: a tree's closes came out
    per subtree (`RtDropOrderRec`: `T6 T7 T3 T1 T4 T5 T2`, natively
    `T7 T3 T6 T1 T5 T2 T4`), and a promise dropped inside Reussir's drain
    ran its dependents there, whose own frees then joined the suspended
    drain (`RtPromiseDepFreeInDrain`: a promise not resolved by its drop;
    `RtPromiseDepWaitInDrain`: a hang).

  The stack is empty whenever the flag is clear: every push happens while
  the flag is set, or a drain follows it (`pending::run_step`; a cell
  pushed outside a drain is released at once, `pending::defer_cell`). An array
  is freed in native Lean's two passes (below): its elements are
  decremented in index order, then those whose last reference went are
  released from the last one, and what an element's release pushes is
  done before the next one.
- **Why:** Lean frees iteratively (`lean_dec_ref_cold`); a value deep
  through containers (a tree whose children are in arrays, chains of
  thunks) overflowed the stack (59b2551). Reussir bounds the stack through
  records, but its glue calls an opaque object's drop hook directly, so a
  chain through boxes or containers would recurse once per level
  (`RtArrayDeepSharedFree`: 10^6 levels on 256 KiB; `RtBoxDeepChain`:
  10^6 nested boxes on 1 MiB). The order: inside a drain, Reussir's
  glue visits a record first field first and depth first, and every
  release on that path that a program can see (a handle, a promise, a
  container, a box) is a leanrt hook that pushes. Popping last pushed
  first gives the reverse of the visit order. That is native's order:
  `lean_del_core` decrements a cell's fields in order and pushes those
  that reach zero, and `lean_dec_ref_cold` pops the last pushed first
  (`RtDropOrderRec`; `RtArrayRecordFreeOrder`: one release of an array of
  structures that hold handles, an array of handles and unresolved
  promises, whose file and dependents fail if elements whose last
  reference goes were released outside the stack, in field order;
  `RtNestedArrayFreeOrder`: a record field before a container field).
  Until the port to upstream Reussir's drop design, Reussir's glue pushed
  record members on one stack shared with leanrt (the old local patches
  02-a to 02-e, [Reussir issue 2](../../reussir-bugs/02-native-drop-order.md));
  since entry 23 the stack is Reussir's own, and leanrt shares it. Two
  differences from native remain (plan
  [§10](../translation-plan.md#10-known-divergences-and-unsupported-features),
  "Order of releases in one free" and "A value shared by two fields of
  one freed cell"):
  - When user code drops a record by itself, no drain runs (a list, a
    structure; a record that Reussir frees as a worklist starts a drain
    only for each of its dead children). Each runtime object that
    Reussir's glue reaches there finds the flag clear, so it is an
    outermost free of its own, which ends before the glue goes on to the
    next member. So the order is field order at every record level from
    the root: a list of handles dropped by itself closes `h1 … hn`
    (natively `hn … h1`, or `h1 hn … h2` where Lean knows the
    constructor). Below the first runtime object or drain, the order is
    native again.
  - Inside a drain, a value that two fields of one cell hold can
    come out at another place: Reussir decrements while it descends,
    while native decrements all fields of a cell first. In
    `R{a : Y{x : W, h}, b : W}`, with `W` held by `Y.x` and `R.b`, native
    closes `Y.h` before `W.h`; leanrt closes `W.h` first, because `W`
    dies at `b` and is pushed last.
- **Where:** `runtime/leanrt/src/pending.rs`: `releasing`, `depth`,
  `defer_step`, `run_step`, `defer_cell`, `drain`, `want_end_work`, over
  reussir-rt's `drop_stack`;
  `runtime/leanrt/src/drop.rs`: `Vec`, `Cell`, `free_vec`, `step_vec`,
  `free_cell`, and the wrappers `active`, `defer`, `run`, `release`;
  `runtime/leanrt/src/task.rs`: `drained`; `scripts/l2r.py`:
  `check_reussir_patches` requires the local patches of the current base
  (`REQUIRED_REUSSIR_PATCHES`: 23-f, 23-k, 23-m, 23-n, 23-o and 07-a), so it refuses the
  checkout of an older base (l2r-base8 and the bases before it push
  onto the old shared stack; l2r-base7, a trial base of the port, freed
  with upstream's destructor executor). Reussir: `lib/IR/RecordDrop.cpp` (`classifyRecordDrop`),
  `lib/Conversion/AcquireDropExpansion/TailDrop.cpp`,
  `lib/Conversion/AcquireDropExpansion/WorklistDrop.cpp`,
  `crates/reussir-rt/src/drop_stack.rs`.
  Tests: `RtDropOrder`, `RtDropOrderRec`, `RtArrayRecordFreeOrder`,
  `RtNestedArrayFreeOrder`, `RtDropDepth3Order`, `RtDepDropOrderBoxed`
  (expectation files: the field order of a free that user code starts),
  `RtArrayDeepSharedFree`, `RtBoxDeepChain`, `RtDropGlue`; leanrt's
  `pending` unit tests; `RtDropSharedSubtree` (expectation files: the
  shared value), `RtDropUserListHandles` (expectation files: a list of
  handles that user code drops closes them first to last),
  `RtDropRefListHandles` (one that `r.set []` frees: native's order),
  `RtPromiseDepFreeInDrain` and `RtPromiseDepWaitInDrain` (no Lean code
  inside a drain), `RtDeepTreeFree` and `RtClosureChainFree` (deep
  worklist frees at native's memory).
- **Remove only if:** never (Lean's order inside a free, and a bounded
  stack through runtime objects). The field order at the top of a free
  that user code starts can only go if Reussir tells the host where such
  a drop starts and ends (not done: a Reussir change).

### Arrays are freed in native Lean's two passes

- **What:** The free of an array of boxes (`drop::free_vec`, `step_vec`)
  first decrements every element in index order (`ReleaseElems::scan`): an immediate is skipped, a shared element
  is decremented in line, and an element whose count is 1 is kept, moved
  to the front of the block (`len`: the number kept). Then the kept
  elements are released from the last one (`release_from_end`), each with
  what it pushes done before the one before it. An array of Reussir
  records (`Bridge` elements: typed arrays, clean step B1,
  [representations/typed-arrays.md](representations/typed-arrays.md))
  is released by its step in index
  order, every element with its own `<record>_ffi_release`, inside the
  free: the counts are not read (clean step A1), the runtime objects a
  freed record holds are pushed, and the pops give native's order for an
  element held twice (freed at its last index) and one that a later
  element also holds (freed inside that element's release). A member that
  two elements share is freed at the second element's place (natively
  after the elements before it: `[R0{X, H0}, R1{X, H1}]`, `X{G}` gives H1 G
  H0, natively H1 H0 G), a deviation that no program sees: lean2rr types
  an array of records only when its elements hold nothing whose release
  the program can observe (the exact order needs a release that decrements
  or, at the last reference, defers: a Reussir entry point, parked);
  leanrt's `drop::tests::record_array_free_shared_inside`. An array of
  `Nat`, `Int` or `String` (typed arrays) is freed at once, inside a free
  or outside one (`free_leaves`): an element's release frees at most its
  own block (a big number, a string), so nothing nests, and no program
  sees the order. Outside a
  running free an array of records is freed at once instead (`free_now`):
  its elements in index order, each with its own `_ffi_release`, then the
  block, without the stack, so a record that an element frees releases
  its members at its own free (by Reussir's glue), not after the elements
  before it are done; the order is not seen for the same reason. That nests (an element's record may hold an array of
  records) up to 16 levels per thread (`FREE_NOW_MAX`); the array at that
  level goes to the stack, whose drain pushes every array below it, so the
  frees stay a loop (freed at once at every level, an array of records
  whose records hold arrays of records recursed once per level and
  overflowed an 8 MB stack, `RtDropDeep`). The step, its drain and
  leanrt's hook at the drain's end (`task::drained`) cost Cedar and
  monadic-interp most of what their arrays of records cost to free (docs: representations/typed-arrays.md, Costs).
  Outside a running free the first pass runs in `free_vec`, and an array
  that keeps no element is freed without the stack; inside one the array
  is pushed, and both passes run when it is popped. It is pushed as one
  pending cell whose release (`push_step_vec`) pushes the array's step:
  the step then runs where a step pushed in the cell's place would have
  run, with the same stack below it, and arrays pushed one after the other
  share one entry of the stack, one pointer (8 bytes) each instead of a
  24-byte step entry. An array that holds nothing counted
  (`ReleaseElems::counts_nothing`: an array of boxes that holds immediates
  only, or an array with no element) releases nothing, so inside a free it
  is freed at once, with no order to keep; one with a shared element is
  pushed (another field of the value being freed may hold that element,
  and its last release comes where the array's pass makes it). A step may run several times (it stops when a
  release pushes work), so the block's header records that the first pass
  is done: `Hdr::_pad` (`SCANNED`, 1; 0 in every live block).
- **Why:** Native `lean_del_core` decrements every element of an array in
  index order, pushing each one whose count reaches zero, and pops them
  last first. The order differs from one pass from the last element when
  an element is shared inside the array: a value held twice is freed at
  its last index, and a value that a later element also holds is freed
  inside that element's release (review of the runtime's speed items,
  finding F1: `RtArrayDupFreeOrder` printed `dcba` and `cba`, natively
  `dbca` and `acb`). The kept elements' counts stay 1 until they are
  released: each is the array's only reference. The first pass is a
  loop, so a deep nesting of arrays still frees on a small stack
  (`RtArrayDeepSharedFree`: 10^6 levels on 256 KiB). Cost (cachegrind,
  small sizes, minimum of two runs, against one pass from the end):
  monadic-interp -0.53 % (its shared elements are decremented in the first
  pass instead of by the step's loop), sieve +0.25 %, qsort +0.31 %,
  liasolver +0.41 % (an immediate costs 5 instructions instead of 4:
  sieve's million-element `Array Bool`); unionfind, binarytrees, deriv
  and rbtree unchanged. Inside a free, Reussir's glue releases a whole
  list or tree within one pop of the stack, so every array it reaches
  waits there at once: as a step each took 24 bytes (review RB-03 of the
  destructor port: a balanced tree of 10^6 nodes, each holding a
  one-element `Array Nat`, freed by a reference's `set`, peaked at 111 MB,
  native 69 MB; a list of such arrays at 105 MB, also before the port).
  Now an array of boxes that holds only immediates is freed at once
  (`counts_nothing`), a typed `Array Nat` too (`free_leaves`), and a boxed
  one is a leaf payload, released directly (box-and-uniform.md): at
  10^6 arrays the tree peaks at 68 MB and the list at 62 MB, native at
  69 MB, with native's allocations and bytes (`RtArrayPileFree`, under
  both integer representations).
- **Where:** `runtime/leanrt/src/drop.rs`: `free_vec`, `free_leaves` (`leaf_elems!`), `free_now` (`FREE_NOW_MAX`),
  `push_step_vec`, `step_vec`, `SCANNED`, `ReleaseElems` (`scan`,
  `release_from_end`, `counts_nothing`) for `LAny` and
  `Bridge`; tests leanrt's `any::tests::box_array_free_shared_inside`,
  `drop::tests::record_array_free_shared_inside`,
  `drop::tests::arrays_inside_a_free_share_one_entry`,
  `RtArrayDupFreeOrder`,
  `RtArrayDeepSharedFree`, leanrt's `drop::tests::leaf_array_free_inside_and_outside`,
  `RtArrayPileFree` (alloc-check: peak memory within native's plus 4 MB).
  The leaf kinds (`Nat`, `Int`, `String`, arrays of scalars) are freed at
  once (`free_leaves`); scalars have no release. A boxed typed array of
  them is a leaf payload (`LEAF_BIT`: `boxLeafArrayElem`), released
  directly, also inside a free (box-and-uniform.md). Inside a record's free,
  before its final drain, the step that a leaf array took drained the
  record's earlier fields at once; freed at once, they stay pending and the
  drain pops them last first, native's order.
- **Remove only if:** never (native's order).

### Arrays of boxes skip immediates and decrement shared payloads inline

- **What:** Freeing an array of boxes (`LAny` elements: every `Array` of
  a Lean type) skips an immediate (an odd word) and decrements a shared
  payload's count inline, without storing the block's `len` or reading
  the stack's depth (`ReleaseElems for LAny`, its first pass `scan`).
  Only a payload whose count is 1 is released (`any::release_last`, or
  its release called in the step: next section), after `len` is set to
  the elements before it, and only then is the depth read (a payload that
  the release pushed is done before the next element). Outside a running
  free, an array none of whose elements is freed is freed without the
  stack at all (`scan` in `free_vec`), and one that keeps one payload or
  leaf releases it without a step (next section).
- **Why:** The generic loop (`release_from_end_each`) stored `len`, dropped
  the element (`LAny`'s drop, inline) and read the depth for every
  element: 12 to 15 instructions an element, and an array of immediates
  (sieve's million-element `Array Bool`) took the stack's step machinery
  (`run`, `step_vec`): sieve 15.0 M instructions in `step_vec`, now 5.0 M
  in `free_vec` (sieve -2.0 %, qsort -3.2 % without mimalloc's free path;
  cachegrind). Skipping immediates four at a time saved 0.25 % more on
  sieve but cost liasolver 0.55 % (its arrays hold pointers), so it is not
  done. The order of releases is unchanged: the elements
  that release nothing come out as before, and a payload freed is
  released at its place, with what it pushes done before the next
  element.
- **Where:** `runtime/leanrt/src/drop.rs`: `ReleaseElems for LAny`; tests
  leanrt's `any::tests::box_array_free`, `RtNestedArrayFreeOrder`,
  `RtArrayRecordFreeOrder`, `RtDropOrderRec`.
- **Remove only if:** never (speed only).

### The array free calls a payload's release where the stack would pop it next

- **What:** Two shortcuts in the free of an array of boxes
  (`ReleaseElems for LAny`). Neither changes the order of releases.
  - *In the step.* The second pass runs as a step of a running free
    (`step_vec`, `release_from_end`). A kept element that is a program
    payload (leaf or not), other than the last kept element, has its
    release called in the step (`any::release_last_in_step`: the
    program's `l2r_any_rel_<num>_c` from leanrt's table) instead of being
    deferred (`any::release_last`). When the release pushed nothing the
    loop goes on with the element before; when it pushed work the step
    returns to the drain, as before. The last kept element (index 0) is
    still deferred. leanrt's own kinds go to `release_last` as before.
  - *Outside a free.* When no drain runs (the stack is then empty), an
    array whose first pass keeps exactly one
    element is freed without a step (`free_single`, called by
    `free_vec`) if that element is a program payload or one of leanrt's
    leaves (a big number, a string, a scalar cell; `any::frees_flat`):
    the block is freed, then the element goes to `any::release_last`. A
    payload that is not a leaf is then released as the drain of that one
    cell (`drop::free_deferred`: `pending::defer_cell` outside a drain),
    a free of its own. A leaf,
    of either kind, is released directly.
- **Why:** MonadicInterp frees about 144,000 old copies of its variables
  array, each holding one count-1 pair of its own, and each went through
  `run_step`, the drain's general loop, `step_vec` and a deferral. Hash
  maps free bucket arrays inside a step, one deferral, one return to the
  drain, one pop and one new call of the step per freed bucket (liasolver
  62,500, hashmap 17,500). Instructions against the same runtime without
  these two shortcuts (cachegrind, small sizes, SVE off, minimum of two
  runs, the `.rr` files identical, outputs equal native, `mi_free`'s
  instructions equal within 0.0001 %): monadic-interp -1.63 %
  (1,055.13 -> 1,037.93 M), liasolver -2.28 % (220.29 -> 215.27 M),
  hashmap -1.25 % (120.84 -> 119.33 M); unionfind -0.01 %, binarytrees
  unchanged. The order:
  - *In the step.* Deferred, the payload's cell would be the only entry
    above the step. The step sees the depth change and returns. The drain
    pops the cell next, and the pop of a run of one cell leaves the step
    as the top entry, so the drain calls the same release with the stack
    as it was in the step. What the release pushes goes above the step in
    both cases, and the depth test returns to the drain, which does that
    work before it runs the step again. When the release pushed nothing,
    the drain runs the step again at once, and the step goes on with the
    element before. So the same releases come in the same order, each
    with the same stack under it. The last kept element stays
    deferred: the block is then freed first, as natively (`lean_del_core`
    frees the array, then pops its elements), and the element is released
    after the step's entry is gone. (A leaf payload is released at once,
    in the step, by `any::release_last`: it frees its own cell and at most
    leaves under it, pushes nothing and has no observable effect, so no
    release can tell the difference.)
  - *Outside a free.* The step would start a drain with the step as its
    only entry. The step frees the block and defers the element (its last
    kept element). The drain removes the step, pops the element and
    releases it with nothing else on the stack, releases what that pushed,
    last first, and ends; its end runs the end work that the free asked
    for (`task::drained`). `any::release_last` does exactly that
    for a payload, without the step: it puts the cell on the stack and
    drains, and the drain pops the cell, releases it, releases what that
    pushed and ends the same way. A leaf (a leaf payload or a leanrt
    leaf) frees its own block and at most leaves under it (a typed array
    of leaf elements frees them at once): it holds no promise and nothing
    further, so outside a drain it pushes nothing and does the same as
    inside one, and the end of the skipped drain would have run nothing (a
    leaf puts off no resolution, and outside a drain no resolution is put
    off: every drain's end runs those put off in it). Natively,
    `lean_del_core` also frees the block and then pops its one element.
    The stack is empty whenever no drain runs, so no work can be pending
    there outside a drain. (With Reussir's old shared stack of local patch
    02-b, a record's glue could leave work pending between the members it
    pushed and its drain; the step then stayed. Reussir's stack since
    entry 23 keeps nothing outside a drain.) An element that is an array of
    boxes keeps the step: released directly, it would be freed by
    `free_vec` again, and a deep nesting of one-element arrays would
    recurse (the unit test `deep_nesting_of_one_element_arrays`: 10^6
    levels on a 256 KiB stack). A `ByteArray` or `FloatArray` element
    would be one `mi_free`, without recursion; it keeps the step only
    because the case is rare.
- **Where:** `runtime/leanrt/src/drop.rs`: `free_vec`,
  `ReleaseElems::free_single`, `ReleaseElems for LAny`
  (`release_from_end`, `free_single`); `runtime/leanrt/src/any.rs`:
  `release_last_in_step`, `frees_flat`. Tests: leanrt's
  `any::tests::box_array_free_releases_in_its_step` (the order, and the
  depth of the stack each release sees, as the deferral's pop gave it),
  `one_kept_element_without_a_step`,
  `deep_nesting_of_one_element_arrays`; `RtArrayFreeDirectOrder`
  (the closes in native's order, through both shortcuts),
  `RtArrayDupFreeOrder`, `RtArrayDeepSharedFree`, `RtBoxLeafRelease`,
  `RtNestedArrayFreeOrder`, `RtArrayRecordFreeOrder`, `RtDropOrderRec`.
- **Remove only if:** never (speed only). It depends on how leanrt's
  drain pops a run of one cell above a step and on how it drains one
  pending cell outside a free (`pending::drain`); if
  either changes, the deferral (`any::release_last` in the step) and the
  step (`run`) are the fallback.

### Array copies of records use the records' own copy

- **What:** Copying an array of records (copy-on-write) clones each
  element with its `Clone`, the record's `<record>_ffi_acquire`; leanrt
  reads no count and decodes no nullary variant (clean step A1). lean2rr
  makes arrays of records with typed arrays (clean step B1,
  [representations/typed-arrays.md](representations/typed-arrays.md)).
- **Why:** No reliance on Reussir's cell layout or its encodings of
  nullary variants (owner, 2026-10-19). Before step A1 the copy
  incremented real boxes in line and skipped immediates (aarch64): under
  Reussir's `tbi` encoding every `nil` bucket of a hash map incremented
  the one static dummy of `nil`, a serial chain through one word
  (Pf4HashPersist 1.04 → 0.80 s; adv4 PF4-11, fe483fe, when arrays held
  records). LLVM inlines `_ffi_acquire` (a Reussir function in the same
  module) into the copy loop.
- **Where:** `runtime/leanrt/src/array.rs` (`CloneInto`, the copy
  paths).
- **Remove only if:** never.
- **Boxes:** an array of boxes (`LAny` elements) is copied with one
  `memcpy` of its words, and then each pointer's payload count goes up
  (`CloneInto for LAny`); an immediate needs nothing. The generic loop
  cloned and stored each box in turn. Test: leanrt's
  `any::tests::box_array_copy`.

### A set releases a replaced record by its own drop

- **What:** An array set (`leanrt::array::set`, the texture
  `l2r_array_set`, behind `Array.set`, `set!`, `uset`, `fset`) releases
  the element it replaces first, then stores the new one, as
  `lean_array_uset`; a pop (`array::pop`) releases the element it removes,
  as `lean_array_pop`. Every element type is dropped by its own drop
  (`ReleaseElem`): in line a handle's decrement, its free out of line; a
  Reussir record (`Bridge`) by its `<record>_ffi_release`, which
  decrements it, frees it (its fields in field order), or leaves a nullary
  variant as it is, through a call out of line (`drop_record`: in line,
  LLVM put the record's whole release into the set texture, which then was
  too big to inline into Reussir code; unionfind's
  `l2r_array_set<nodeData>` stayed a call, 6.56 G instructions in all
  against 5.89 G with the call). An array of boxes (rule 1) drops a replaced box: only the
  decrement in line (`LAny::drop`: an immediate skipped, a count above 1
  decremented), and the last reference goes to `any::release_last`, which
  frees a program payload as one pending cell (next section).
- **Why:** lean2rr makes an array of records only when its elements hold
  nothing whose release the program can observe (typed arrays,
  [representations/typed-arrays.md](representations/typed-arrays.md#only-elements-whose-releases-cannot-be-observed-are-typed)),
  so the order in which a freed record releases its fields is not seen.
  Until clean step B1, every removed record went to `array::release_last`
  (`#[inline(never)] extern "C"`), shared or not, which released it inside
  a free the runtime starts (`drop::release_unique`), so that its fields
  went in Lean's order, the last one first (the record's own release
  frees the first cell's fields in field order: a structure of two handles
  `{a, b}` replaced by a set closed `a b`, natively `b a`; review RS10-01
  of switch step 10; tests `RtArraySetFreeOrder`, `RtArrayPopFreeOrder`,
  whose arrays of handles stay boxed). That free cost about 74
  instructions per set, also for a shared record: n-body with typed
  arrays ran 760 M instructions with it, 493 M with the record's own drop
  (602 M with arrays of boxes). `tests/runtime/ffi-inline-check.sh`
  builds `RtArraySets` (sets of every element representation in loops,
  typed records among them) to LLVM IR and fails when a set's texture or
  function stays a call. At a call site that LLVM judges cold (deep in
  branches) every set texture, of any element type, is still a call
  (Reussir issue 6, not patched).
- **Where:** `runtime/leanrt/src/array.rs`: `ReleaseElem`, `drop_record`,
  `set_in`, `pop_in`, `release_last` (kept, unused, for element types
  whose release order is seen); tests `RtArraySets`, `RtArraySetFreeOrder`,
  `RtArrayPopFreeOrder`, `RtTArrInPlace`, `tests/runtime/ffi-inline-check.sh`.
- **Remove only if:** lean2rr types arrays whose elements may hold an
  observable value: their sets need `release_last` again.

### A record is released as one pending cell

- **What:** `drop::release` (reference and cell sets) and
  `drop::release_unique` (`array::release_last`, unused since clean step
  B1: a set or a pop of a record drops it, previous section) release
  a record (`Bridge`) with `drop::free_unique`, shared or not: leanrt does
  not read a record's count or decode Reussir's nullary variants (clean
  step A1). `drop::free_deferred` defers the record as one pending cell
  (`pending::defer_cell(p, release_record::<X>)`: the stack writes nothing
  into the cell).
  - Outside a drain, that is the outermost free (the drain of one cell:
    the stack's `defer` outside a drain). It sets the flag, releases the
    cell at once, and `release_record` runs the record's `<record>_ffi_release`.
    Reussir's glue visits the fields first field first; every runtime
    object it reaches is pushed, and the pops release them last first.
    The drain goes through its general loop only when the release pushed
    work. At its end it runs the end work that a release asked for
    (`task::drained`: the promise resolutions put off, then
    `after_drain`).
  - Inside a drain (leanrt's or Reussir's glue's), the cell is only
    pushed (it joins the run on top if that run has the same release
    function; else the run on top moves to the vector), and the drain
    releases it when it pops it.

  The record's `<record>_ffi_release` frees it, or only decrements a
  shared one, or leaves a nullary variant as it is. Before step A1 a
  shared record was decremented in line and an immediate skipped
  (aarch64), and only the last reference took this path. The last
  reference to a box's program payload is freed
  the same way, on every target (`LAny`'s count is always tested):
  `any::release_last` gives the payload's cell (the box's word without its
  number) to `drop::free_deferred` with `release`, the program's release
  of the payload's type, found by number in leanrt's table
  (`l2r_any_rel_<num>_c`, box-and-uniform.md; cells with one release
  function share one entry: box-and-uniform.md, "Pending cells with one
  release function share one entry"). A leaf payload is released
  directly, inside a free too (it frees its own cell and at most leaves
  under it: a typed array of leaf elements frees them at once). This covers
  boxed records replaced or removed in an array, a reference's or cell's
  old value, and any other box dropped for the last time.
- **Why:** At switch step 10 the record was a step (`drop::run`:
  `run_step` writes a `Work::Step` into the stack's vector, the drain
  dispatches it and moves the entries above it down with `memmove`):
  about 140 instructions per freed record (`drain_slow` 64, `run_step` 33,
  `step_record` 11, `release_last` 11, `memmove`/`memcpy` 13,
  `free_record` 3). As one pending cell: about 74 (cachegrind, the loop
  of 300,000 sets each freeing a record of five `UInt64`s: `drain_one` 26,
  `__reussir_drop_drain` 18, `__reussir_drop_defer` 17, `release_last` 7,
  `release_record` 6 with the record's own free). These numbers were
  measured on the old local Reussir stack (the same code, later leanrt's
  own `pending`, now Reussir's drop stack again, called from Rust
  instead of through C symbols; outside a drain one cell is now released
  without being pushed); they were not measured again. The order is the same:
  in both forms the record's release runs inside the drain on top of the
  stack as it was, and the stack is popped last pushed first. Totals
  (step 10 in brackets): unionfind +0.8% against dev d39294a (+5.0%);
  the micro loop 58.1 M instructions (77.9 M; dev 9a2ddf6 35.7 M), with a
  record of two strings too 87.4 M (109.6 M; dev 9a2ddf6 73.3 M); 16 of
  the other 17 classic programs as at step 10 (within 0.02%), and
  binarytrees +2.9%
  from code layout only (an
  identical `.rr`; `check` has four alignment `nop`s before its loop,
  executed once per call, and an erratum-843419 veneer moved to a load
  in `make'`). The three calls (defer, drain, the one-cell drain) could
  be one entry point of leanrt's own; the gain measured for that entry
  point in Reussir's runtime was small (monadic-interp -4.99%
  instructions, unionfind -2.52%; owner, 2026-10-07).
- **Where:** `runtime/leanrt/src/drop.rs`: `release`, `release_unique`,
  `ReleaseValue`, `free_unique`, `free_deferred`, `release_record`;
  `runtime/leanrt/src/pending.rs`: `defer_cell`, `drain` (reussir-rt's
  `drop_stack::defer`, `drain`);
  `runtime/leanrt/src/array.rs`: `release_last`;
  `runtime/leanrt/src/any.rs`: `release_last`; `runtime/leanrt/src/drop.rs`:
  `free_deferred` (a wrapper of `pending::defer_cell`). Tests: leanrt's unit tests
  `drop::tests::record_free_order` and `record_free_inside_a_free`;
  `RtArraySetFreeNested` (a set, a pop and a reference set freeing
  structures that hold structures and a list), `RtArraySetFreeOrder`,
  `RtArrayPopFreeOrder`, `RtRefSetOrder`, `RtPromiseFreeLaterUnresolved`.
- **Remove only if:** leanrt's stack changes what a pending cell does
  (the drain releases it with the given function and writes nothing into
  it) or what a drain of one pending cell does; then the step (`run`) is
  the fallback.

### Reads give their reference up first, for a view

- **What:** Every FFI call consumes its arguments, so an array read is the
  caller's increment and the read's decrement. A read gives its reference
  up before anything else: `l2r_array_give` (`leanrt::array::give`)
  decrements a shared array
  and returns a *view*, a `u64`: the block's address, with bit 0 set for a
  shared array (the last reference keeps its count of 1, bit 0 clear). The
  bounds check comes next, in Reussir code (`l2r_view_size`); then
  `l2r_view_take` clones the element (the last reference then frees the
  block out of line, `free_vec`), or `l2r_view_end` ends the view (`get!`
  out of bounds). Nothing is released between `give` and `take` or `end`:
  `get!` releases its default in bounds after the take (`l2r_consume`, a
  use that keeps it alive until then), where Reussir would release it at
  the start of the branch. The failing branch
  of a read that a proof keeps in bounds releases nothing and ends the
  program: an index word from 2^63 (a big `Nat`) is
  unreachable code, another `index_bug` (`l2r_index_fail_w`,
  `l2r_array_index_bug`). String reads decide their release before their
  rule runs (`leanrt::string::read_owned`); `get_fast`/`next_fast` take
  the position's word, and one from 2^60 is unreachable code inside the
  texture (`l2r_string_get_fast_k`, `l2r_string_next_fast_k`,
  `leanrt::unreachable_code`); the `Pos.Raw` reads turn a big position
  into `u64::MAX` without a call (`l2r_index_sat`) and release it after
  the read (`l2r_consume`).
- **Why:** LLVM removes the increment and the decrement together only when
  no call and no other store come between them on any path (Reussir's
  `rc.inc` lets it assume the old count was at least 1; so do the
  runtime's clones of array and string handles, such as a constant's read,
  `l2r_once_get`: [startup/constants.md](startup/constants.md), "A read of
  a constant is one load"). Three earlier
  forms kept them (lean-zip's LZ77 loop, count stores on its hot paths;
  perf-array-reads): the texture checked the bounds and released after
  (the panic's call came between: 77 stores; and 279 of lean-zip's array
  reads stayed calls, too costly for LLVM); a check in Reussir code before an
  unchecked texture left a release in the failing branch, so the
  increment had two decrements, one on each side, and dead-store
  elimination needs one store that overwrites it on every path (58); one
  checked texture that decrements first costs 55 in LLVM's inline cost
  model, above its threshold for a cold call site, 45 (41 of the loop's
  reads stayed calls; [Reussir issue 6](../../reussir-bugs/06-trampoline-inline.md),
  a missed optimization, not patched). Split into `give`, `size` and
  `take`, each texture is small enough for a cold call site: no read stays
  a call, and the loop has 47 hot stores, at most 7 on one iteration (15
  before). With the one-word `Box` the read of a box is over that
  threshold again (`view_take<LAny>`: the copy of a box tests its low bit
  and masks its top bits), and so are the reads of a `Nat` or `Int`
  element at its type (`view_take_as`): at a cold call site they stay
  calls (`tests/runtime/ffi-inline-check.sh` allows this in `RtReadsDeep`
  only).
  Bit 0 is set for the shared case because LLVM does not know that the
  block's address is even: after the caller's increment it sees the view
  `o | 1` and folds the test; with the bit set for the last reference it
  kept the test, unswitched loops on it and kept the clone of a record
  element. `view_take` clones in line on both of its paths, so that a
  later release of the element cancels against the clone. `get!`'s default
  released at the start of the in-bounds branch could hold the other
  reference to the array (a tree's child or the tree itself, `cs[i]!` with
  the tree as the default; a closure that captures the array): it freed
  the block the view then read (review PAR-01, test `RtArrayGetDefault`).
  Out of bounds, `get!` panics before it ends the view, as natively the
  panic comes inside the extern and the caller's release of the array
  after it: what freeing the array releases (a handle's flush) follows the
  message, and under `LEAN_ABORT_ON_PANIC` does not happen (review HA-01,
  test `RtArrayGetOobOrder`).
  Left to LLVM: a
  loop body whose slow path (a big number's `nat_add`, a call) rejoins the
  fast path keeps a count store per iteration. GVN reloads the count after
  the call, so the count becomes a phi: LLVM can no longer tell that it is
  above 1, or the store writes a phi of loads back, which dead-store
  elimination does not take for a no-op (one store per iteration in a
  `ByteArray` sum over a `USize` index; in lean-zip's `ugetUInt32LE`, an
  increment and a decrement per call). The increments before calls that
  take the array (`updateHashesMerged`) are the cost of owned parameters,
  not of reads.
- **Where:** `runtime/prelude.rr`: `l2r_array_give`, `l2r_view_size`,
  `l2r_view_take`, `l2r_view_end`, `l2r_array_get`, `lean_array_fget_w`,
  `l2r_index_fail_w`, `l2r_array_index_bug`, `lean_array_get`,
  `lean_byte_array_get`, `lean_float_array_get`, the string reads;
  `runtime/leanrt/src/array.rs`: `give`, `view_size`, `view_take`,
  `view_end`; `string.rs`:
  `read_owned`; `lib.rs`: `unreachable_code`; tests `RtArrayReadViews`,
  `RtArrayGetDefault`, `RtReadsDeep`, leanrt's unit tests `views`; plan §10
  ("Reads take their container owned").
- **Remove only if:** Reussir gets borrowed FFI parameters (a feature
  request; plan [§9](../translation-plan.md#9-open-items)). A view is
  valid only while nothing else runs between `give` and `take` or `end`:
  no Lean code (one thread runs Lean code, and the bounds check calls
  none), and no release of another owned value that Reussir inserts there
  (a value used only on one branch is released at the branch's start: such
  a value must be consumed after the take, as `get!`'s default is).
  `tests/runtime/ffi-inline-check.sh` checks that the read textures stay
  inlined at cold call sites (`RtReadsDeep`).

### A read's index is passed in a `let`

- **What:** lean2rr binds the `Nat` arguments of a read extern (`a[i]'h`,
  `a[i]!`, the byte and float arrays' reads, the string reads at
  a `Nat` position: `readExternSyms`) by a `let` before the call:
  `let k = i; read(a, k)`. That is the index. A parameter declared at a
  type variable (`get!`'s default, at `Array Nat` a `Nat`) is left out
  (`atVar`): its argument is in its storage, a `Box`, and since the
  boxing of a box unboxed at once folds away (`boxUnboxed?`), a box field
  passed as the default is the box variable itself, which a `Nat` `let`
  would mistype (the classic `sieve`'s `omega` passes such a default).
  `String.Pos.Raw.get?` goes through
  lean2rr's glue (`Lower/Externs.lean`, `lean_string_utf8_get_opt`) and is
  not covered.
- **Why:** Reussir increments a variable that is used again later where it
  is used, the arguments of a call from left to right. As a direct
  argument, an index used after the read (`a[i]`, then `i + 1`) was
  incremented after the array; the increment of a big index is a store
  that LLVM cannot tell from the array's count, and between the array's
  increment and the read's decrement it made LLVM reload the count and
  keep both. With the `let`, Reussir increments the index at the `let` and
  the array at the call, the last store before the read. Reussir keeps the
  `let` (its front end does not propagate copies). Lean-zip with the
  runtime's reads above: the LZ77 loop's hot stores 72 → 47,
  `updateHashesMergedH3FastU` 12 → 4.
- **Where:** `Lower/ExternCall.lean`: `readExternSyms`, `bindReadIndex`,
  both final calls of `lowerExternCall`.
- **Remove only if:** Reussir gets borrowed FFI parameters, or increments
  a call's arguments in another order.

### A thunk's cell gives up its closure before running it

- **What:** Forcing a pending thunk or task swaps `busy` into the cell,
  runs the closure it took out, and stores `done(v)`, which Reussir can
  build in the cell the pending state frees.
- **Why:** As `lean_thunk_get_core`, which takes the closure out before
  calling it: the cell no longer holds it, so the closure and its captures
  are released as soon as it has run.
- **Where:** `Lower/LazyForce.lean`: `lazyGetFn`; see
  [tasks/cells.md](tasks/cells.md).
- **Remove only if:** never.
