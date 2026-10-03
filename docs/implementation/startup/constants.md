# Constants and closed terms

Paths: `lean2rr/LeanToReussir/` for lean2rr's files, `runtime/` for the
runtime. Plan
[§5.12](../../translation-plan.md#512-constants-cafs-and-closed-terms).

### A constant is a once-cell read through an accessor

- **What:** A declaration without parameters becomes `<f>_init` (its
  body) and an accessor `<f>` that tests the constant's once-cell inline
  (`l2r_once_claim`), reads it if set, and otherwise computes and stores
  the value. The cell stores a boundary type; another value is wrapped in
  an `ElemBox`. The value is never freed. Program constants are forced at
  startup ([order.md](order.md)); toolchain constants and closed terms
  only on first use.
- **Why:** Native CAFs and closed terms live for the whole run, evaluated
  once. `l2r_once_claim` also makes a scheduler context that needs a
  constant another context is computing wait for it, as natively
  `lean_obj_once_cold` holds a lock: it was computed twice and the runtime
  aborted ("once slot set twice", 7edc0f5). Its fast path is inline again
  (the scheduler had made every constant read a call; perf5, 32db458).
- **Where:** `Lower/Conv.lean`: `cafAccessor`; `Lower/Code.lean`:
  `lowerDecl`; `runtime/prelude.rr`: `l2r_once_claim`, `l2r_once_get`,
  `l2r_once_set`; `runtime/leanrt/src/once.rs`: `claim`.
- **Remove only if:** Reussir globals replace once-cells (plan
  [§7](../../translation-plan.md#7-optimization-what-is-already-done-and-what-is-left),
  "globals for constants"). Cost: a constant read in a loop checks its cell
  every time (Pf4BigLit 1.16x native).

### Cheap constants are recomputed, float literals folded

- **What:** A constant that only builds unboxed values from small
  literals, constructors and total scalar conversions is recomputed at
  each use (`cheap-consts`); a float literal (`Float.ofScientific` on
  literals) is evaluated by lean2rr and becomes `Float.ofBits` of its bit
  pattern (`float-lits`).
- **Why/Where:** see [../optional-passes.md](../optional-passes.md).
- **Remove only if:** they are optional passes: without them only speed
  changes.

### A closed term used once, by another constant, is not cached

- **What:** A closed term referenced exactly once, from a constant (not
  from a function, not a root of the entry point), is evaluated where it is
  used instead of being kept in a once-cell. It still runs once, at the
  same point.
- **Why:** Lean's `extractClosed` makes an `n`-element literal a chain of
  closed terms `_closed_k := push _closed_(k-1) e_k`; caching every step
  kept every intermediate array alive: memory quadratic in the literal's
  length (10000 elements: 1036 MB instead of 7 MB; adv2 N5, fbf37e8).
- **Where:** `Emit/Program.lean`: `chainConsts`; `LowerBase.lean`:
  `LowerCtx.uncachedConsts`; `Lower/Code.lean`: `lowerDecl`. Required part
  `closed-chains` in `Opt/Registry.lean`.
- **Remove only if:** never.

### Straight-line chains are spliced into their user

- **What:** When such a closed term's code and its user's are straight-line
  (`let`s, then `return`), it is spliced into the user before lowering:
  the chain becomes one straight-line body, each literal placed right
  before its first use. Only chains where nothing but literals (or reads of
  closed terms of literals) is computed before a step reads the previous
  step are spliced.
- **Why:** rrc compiles about 80 functions per second: a 100000-element
  `Array Nat` literal as 100000 functions took ten minutes to build (adv3
  Cn3ArrLit100k, 7c4ab5c). An `Array Float` literal whose elements are
  shared constants, spliced, computed every element before the whole rest
  of the chain (a 55 MB `.rr`, 538 s and 4.3 GB to build; e52c1d3). The
  splice uses an explicit stack, linear in the chain.
- **Where:** `Emit/Program.lean`: `spliceChainConsts`, `spliceChains`,
  `spliceable`, `literalsOnly`, `straightLine`, `SpliceFrame`. Long
  spliced bodies are then cut by
  [../control-flow/outline.md](../control-flow/outline.md).
- **Remove only if:** rrc's per-function cost drops by orders of
  magnitude.

### Long `Array Nat` literals become tables

- **What:** In the generated code, a run of 32 or more small `Nat`
  literals pushed onto an `Array Nat` (each literal and each intermediate
  array used only there) becomes one call `l2r_natarr_lits(a, id)`, which
  pushes the words of table `id`, generated with the program. Only with
  `nat-arrays` (it matches `lean_natarr_push`).
- **Why:** rrc costs about 0.3 MB per `Nat` operation in a straight-line
  function ([Reussir bug 17](../../../reussir-bugs/17-long-nat-block.md));
  a 100000-element literal is now one call (7c4ab5c, test `RtArrayLit`).
- **Where:** `ArrayLits.lean`: `natArrLits`, `tableLets`, `smallLit?`,
  `minRun`, `natLitTable`; `Emit/Program.lean`:
  `LoweredProgram.literalTables`.
- **Remove only if:** bug 17 is gone (and the build stays fast without
  it).

### A constant that may hold tasks waits for them

- **What:** When a constant whose type may hold a task is first computed,
  `l2r_persist_T` walks its value and waits for every task it reaches:
  through fields, arrays, the values of tasks, the values captured by
  function values, thunks (their computation or value, without forcing
  them), references (their value) and `Box` payloads. The walks are
  generated at the end, once every variant of function types and `Box` is
  known; a type that cannot hold a task gets none.
- **Why:** As `lean_mark_persistent` at a closed term's first evaluation:
  a `Task.spawn` extracted as a closed term has finished once the term has
  been used (adv4 TK4-02, a599e0a; closures, thunks and boxes: 17ab235;
  references: round 7 RV7L-05, test `RtPersistRef`). The searches for
  task-holding types look at each type once: following every path took
  over ten minutes on polymorphic-recursion towers (1955043).
- **Where:** `Lower/Conv.lean`: `persistCall`, `mayHoldTask`,
  `persistFnName`, `cafAccessor`; `Lower/Finish.lean`: `holdsTask`,
  `persistCell`, `genPersist`, `finishPersistFns`, `variantCount`. Plan
  §5.14 (*Closed terms*).
- **Remove only if:** never.

### The walk is a loop over a work list, each cell once

- **What:** `l2r_persist_walk(h, w)` loops over a work list `L2RPersistW`
  (a variant per type that can hold a task, one per array type for the
  elements left); `l2r_persist_x_T` pushes what a value holds. A cell
  (record, array, thunk or task, function value, `Box`, reference) is
  looked into once: `l2r_persist_seen` keeps the walk's set of addresses
  (`runtime/leanrt/src/persist.rs`).
- **Why:** The recursive walk overflowed the stack on a value deep through
  a non-last field (300000 links at the 8 MB startup stack, even for an
  unused constant) and walked a shared DAG as a tree (41 cells, 2^40
  paths): round 7 RV7L-01, 42517bf, tests `RtPersistWalk`,
  `RtTaskConstDeep`.
- **Where:** `Lower/Finish.lean`: `genPersist`, `finishPersistFns`,
  `persistListName`, `persistCell`; `runtime/leanrt/src/persist.rs`;
  prelude `l2r_persist_begin/seen/keep/end`. Plan §5.14, §10 (stack
  depth).
- **Remove only if:** never (any recursion is bounded by the stack).

### The walk's order is native's: last field first

- **What:** Fields are pushed in Lean's declaration order (`leanOrder`,
  whatever the record layout), the last on top; an array is walked from
  its last element down (`a<T>(array, index, rest)`).
- **Why:** The tasks of a freshly evaluated closed term have not started,
  so they run in the order the walk reaches them, and their traces and
  panics show it. Native `lean_mark_persistent` pushes fields, captured
  values and elements in order and pops the last first: `(t2, t1)` runs
  `t1` first, `#[a0, a1, a2]` runs `a2` first. Round 7 RV7L-04, test
  `RtPersistOrder`.
- **Where:** `Lower/Finish.lean`: `genPersist` (`each`, `arm`'s `order`,
  `leanOrder`, the array step `l2r_persist_a_T`). Plan §5.14.
- **Remove only if:** native's walk order changes.

### The walk keeps what it reads out of thunks, tasks and references

- **What:** Each value read out of a thunk's or task's state or a
  reference's cell is kept (`l2r_persist_keep`) until the walk ends.
- **Why:** Every other path to a visited cell goes through immutable
  fields of the constant, which its caller holds; these do not (a task the
  walk runs can force a thunk, which drops its computation). A visited
  cell freed meanwhile could give its address to a new cell, which the
  visited set would then skip (RV7L-01 fix).
- **Where:** `Lower/Finish.lean`: `genPersist` (`each … keep`);
  `runtime/leanrt/src/persist.rs`: `keep`, `end`.
- **Remove only if:** the visited set stops using addresses.

### The walk is skipped when every task has finished

- **What:** `l2r_persist_T` returns at once when `l2r_task_settled()`: no
  task has an entry in the runtime's table.
- **Why:** Waiting for a finished task does nothing, so the walk would
  only cost time and memory; at startup tasks run at once, so constants
  evaluated then are never walked (RV7L-01 fix).
- **Where:** `Lower/Finish.lean`: `finishPersistFns`;
  `runtime/leanrt/src/task.rs`: `settled`.
- **Remove only if:** an unfinished task can exist without an entry (then
  the skip would be wrong and must go).
