# Calls and `let`s

Paths are relative to `lean2rr/LeanToReussir/` unless they start with
`runtime/`.

### Calls follow Lean's arities exactly

- **What:** A call with exactly the callee's arity (the number of
  parameters Lean gave it after its optimizations, erased ones included)
  runs it; fewer arguments build a partial application (a `p` variant,
  nothing runs); more arguments run it and apply the result to the rest.
- **Why:** Where work runs is observable: the native build of
  `mkAdder` with a `dbgTrace` before its inner `fun` has arity 2 and prints
  once per call of `mkAdder 3 x`; a translation at arity 1 prints once in
  total.
- **Where:** `Lower/Values.lean`: `lowerConstApp`; `Lower/Decls.lean`:
  `calleeOf`, `partialApp`, `applyChain`; plan
  [§5.2](../../translation-plan.md#52-declarations-calls-arities).
- **Remove only if:** never.

### Erased parameters are removed (rule 4)

- **What:** A Reussir function takes no parameter for an erased Lean
  parameter (`◾`: a type, a type argument, a proof; `erasedDom`), except
  its last parameter: when that one is erased, the function takes one
  `L2RUnit` for the trailing erased parameters (`keepMask`). Example:
  `def f (x : Nat) (α : Type) (y : Nat) (β γ : Type)` becomes
  `f(x : Nat, y : Nat, u : L2RUnit)`, and `def el {α} : List α` keeps
  `el(u : L2RUnit)`. A removed parameter is bound to `L2RUnit::u{}` in the
  body. A call passes the arguments of the parameters the function takes
  (`()` for the trailing unit); a partial application captures those among
  the arguments it has (`p<j>` counts Lean arguments). Targets of function
  values (externs, constructors) follow the same rule, and their call gets
  placeholders back at Lean positions (`targetCall`), as a direct call of
  them has. Join points take no erased parameter at all; their jumps drop
  those arguments. The IO world (`lcVoid`) and `Unit` are data, not
  erased. Stage 1 to 3 keep Lean's arities; only Stage 4 removes.
- **Why:** `◾` carries no information. Keeping the last erased parameter
  keeps the point where the body runs: Lean runs a body when the last
  parameter is applied, so `f 3` of `def f (x : Nat) (α : Type)` must stay
  a partial application that runs `f` only when the type is applied (map C
  hazard H2), and a function with only erased parameters must stay a
  function (H1, review finding fixed in 4674426). Lean's passes, closed
  terms (`ExtractClosedK`), `chainConsts`, the startup `.caf` items and
  `safeToElim` decide on Lean's arities (H9), so the removal is in Stage 4,
  keyed on LCNF parameter lists.
- **Where:** `ErasedDomains.lean`: `erasedDom`, `keepMask`;
  `Lower/Code.lean`: `lowerDecl`, the `.jp`, `.jmp` and `.fun` cases, the
  state machine's self call; `Lower/Decls.lean`: `calleeOf`;
  `Lower/Values.lean`: `lowerConstApp`, `lowerTaken`, `ctorFnType`;
  `Lower/Borrow.lean`: `boxedTarget` (Lean's borrow flags by Lean
  position); `Lower/Finish.lean`: `targetCall`; tests `RtErasedTrailing`,
  `RtErasedTypeOnly`, `RtErasedMid`.
- **Remove only if:** never (it is rule 4 of the dependent-types design).

### Lean's `let`s that can have an effect are never dropped, duplicated on a path, or reordered

- **What:** Lowering adds bindings of its own (conversions, placeholders,
  copies of duplicated join points, one per path) but keeps every Lean
  `let` that can have an effect, in order, once per path.
- **Why:** A `let` can call a function that panics or traces; Lean's
  passes have already removed dead `let`s.
- **Where:** `Lower/Code.lean`: `lowerCode`; plan
  [§5.4](../../translation-plan.md#54-let-return-literals).
- **Remove only if:** never.

### Effects are kept in order by opaque FFI calls

- **What:** The IO world is only an `L2RUnit` value; what orders effects
  is that IO, `ST.Ref`, panic and trace operations are effectful FFI calls,
  which Reussir and LLVM never merge, drop or reorder. lean2rr relies on
  the same property to place a release after a call
  (`l2r_release_after`).
- **Why:** Nothing else would stop Reussir or LLVM from merging two
  identical `println` calls (probe results, plan
  [§9](../../translation-plan.md#9-open-items)).
- **Where:** `runtime/prelude.rr` (`#[ffi(import)]` functions);
  plan [§5.8](../../translation-plan.md#58-externs-and-runtime-calls)
  ("Effects are never optimized away").
- **Remove only if:** never.

### A run of `let`s is lowered in a loop

- **What:** `lowerCode` lowers a run of `let`s in one loop, each value
  with a map of just the variables it reads; the run's own variables
  collect in a map merged once at the end.
- **Why:** Growing the context's map copied it at every `let`, so a long
  straight-line body (a spliced literal) cost quadratic time (7c4ab5c).
  The output is the same.
- **Where:** `Lower/Code.lean`: `lowerCode` (the `.let` case).
- **Remove only if:** never.

### The boxes of a constructor that takes a self call's result are bound before the call

- **What:** Lean's code for `x :: xs => (x + 1) :: inc xs` is
  `let y := x + 1; let r := inc xs; let c := List.cons y r`. The cell's
  field is a `Box`, and the boxing of `y` is written inside the
  constructor (`lowerArg`), after the self call:
  `let r = l_inc(xs); T_List::c_cons{l2r_any_of_nat(y), r}`. When a `let`
  is a saturated call of the declaration being lowered, in the code of
  its own function, the next `let` is a saturated constructor
  application that takes the call's result as a field, and the code
  after it returns that constructor's value as it is, each other
  argument of that constructor that is a variable, taken once, at a field
  of type `Box`, with a type of its own that is not `Box`, and whose
  conversion is a pure boxing, has its box bound before the self call:
  `let hb = l2r_any_of_nat(y); let r = l_inc(xs); T_List::c_cons{hb, r}`.
  A pure boxing (`pureBoxExpr`) is a call of the prelude's boxing
  functions (`l2r_any_of_nat`, `l2r_any_of<T>`, `l2r_any_of_ptr<T>`,
  `l2r_any_of_u64`, `l2r_any_of_f64`, `l2r_any_imm`, `l2r_any_unit`, the
  scalars'), of a generated `l2r_box_T`, of an enumeration's index
  function or of a boxed constant's accessor, on variables, literals,
  numeric casts, a `[value]` struct's field and an `ElemBox` around the
  value. Every other conversion stays in the constructor. The box is
  named after the call's variable (`hb815` before `x815`), not by the
  program's counter, so the numbering of the rest of the program does not
  change.
- **Why:** Reussir turns a self call whose result only goes into a
  constructor into a loop (tail recursion modulo cons). Since upstream
  #984 it keeps the self call in place when a call stands between it and
  the constructor, which is correct: a traced or panicking call written
  after the recursion must run after it (test `RtTrmcCallOrder`: `g2 g1
  g0`; the base before #984 printed `g0 g1 g2`). Reussir cannot know that
  a boxing has no effect (it ends in an FFI function), so every list or
  tree map with a boxed element lost its loop: of 57 functions with a
  loop on the old base in 26 programs (the classic corpus and 8 others),
  10 kept it; with this rule 54 have one (classic corpus: 30, 7, 29).
  The other 3 are right without one: two apply a closure after the self
  call, and `AssocList.foldrM` builds a pair after it (Lean's order of
  `let`s is kept).
  With an 8 MiB stack (`LEAN_STACK_SIZE_KB=8192`) a map over 10^6
  elements runs again; without the rule it stops with native Lean's
  "Stack overflow detected", as native does. A boxing reads the variable
  and makes a box: an immediate, a new cell around a word (`Float`, a
  `UInt64` from 2^63), or the value's own pointer with a payload number.
  It cannot panic, print, run code of the program or release anything
  (the box takes the variable's reference, or a retained copy when the
  variable is used again), and the number of references to the value
  during the self call is the same. So only an allocation moves. An
  unboxing is not moved: it can release its box, and in a program that
  casts it can end in a panic. Cost: where Reussir makes no loop and the
  box is a cell, the cell is made before the recursion and not after it,
  so one more cell is live per level while the recursion runs; the number
  of allocations is the same. Measured without the `return` condition: a
  map of 4 x 10^6 `Float`s that passes each new cell to a call peaked at
  412.9 MB for 349.3 MB (16 bytes per level; native Lean 506.7 MB). So
  the rule asks for the `return`: a constructor whose value the function
  uses again never gives a loop, and that program is translated as
  before.
- **Where:** `Lower/PreBox.lean`: `preBoxArgs`, `pureBoxExpr`,
  `pureBoxFns`; `Lower/Code.lean`: `lowerCode` (the `.let` case),
  `lowerDeclCode` (`CodeCtx.ownFn`: off in a state machine, an outlined
  join point's function and a local function); `Lower/Decls.lean`:
  `lowerArg` (`CodeCtx.preBoxed`); test `RtTrmcCallOrder`;
  `tests/runtime/trmc-helper-check.sh` (the `.trmc` helpers of
  `TrmcHelper.lean`: present for the box-only shapes, absent after a
  traced call).
- **Measured:** timing run 20 (2026-11-18; the port against the port
  without the rule; direct pairs, median of 9 and min; the 21 cases of
  the shared benchmark set whose code the rule changes): geometric mean
  1.018. Two cases gain: E02 merge_sort_list 1.223 and X12 k_nucleotide
  1.064. The other 19 show no measurable effect, and no case is slower
  with the rule (the fastest ratio without it is 0.995). Peak memory
  without the rule: 1.67 times on E02 and 1.23 times on L13 mergesort
  (whose time does not change: 1.004).
- **Remove only if:** Reussir's tail recursion modulo cons learns that a
  callee is pure and total (an attribute on functions and FFI imports), or
  boxes are no longer calls. Without the rule the programs are still
  correct; the functions recurse, as natively.

### Constructors implemented by the runtime are calls

- **What:** Constructors of builtin types that carry an `@[extern]`
  (`Int.ofNat` is `lean_nat_to_int`, `Int.negSucc`, `ByteArray.mk`, …) are
  extern calls; `Thunk.mk` and `Task.pure` get glue.
- **Why:** As in Lean's IR; they are not constructors of `Int` (runtime
  request 1, f67bbec; 4674426).
- **Where:** `Lower/Decls.lean`: `calleeOf`; `Lower/LazyGlue.lean`:
  `lazyExtern`.
- **Remove only if:** never.

### Panics continue; `unreachable` stops the program

- **What:** `panic!` prints the message native prints (`PANIC at …`) and
  then `backtrace:` and `(stack trace unavailable)` where native prints the
  frames (unless `LEAN_BACKTRACE=0`, which prints neither; a divergence of
  plan §10), through the current stderr stream, and returns the default
  value;
  `LEAN_ABORT_ON_PANIC` aborts. `unreachable`, and lean2rr's own
  impossibilities (a `Box` unwrap of another variant, a cast with no
  conversion), print `INTERNAL PANIC: unreachable code has been reached`
  and exit 1.
- **Why:** Native behaviour; lean2rr's impossibilities look like Lean's
  own (plan [§5.9](../../translation-plan.md#59-panics-and-unreachable-code)).
- **Where:** `runtime/prelude.rr`: `l2r_panic_text`, `l2r_panic_str`,
  `lean_panic_fn`, `l2r_unreachable`, `l2r_internal_panic`; lean-runtime's
  `io::panic` (`report`, `internal_panic`), through `runtime/leanrt/src/lib.rs`
  ([../externs-ffi/runtime.md](../externs-ffi/runtime.md), switch step 8).
- **Remove only if:** never.
