# Constants and closed terms

Paths: `lean2rr/LeanToReussir/` for lean2rr's files, `runtime/` for the
runtime. Plan
[§5.12](../../translation-plan.md#512-constants-cafs-and-closed-terms).

### A constant is a once-cell read through an accessor

- **What:** A declaration without parameters becomes `<f>_init` (its
  body) and an accessor `<f>` that tests the constant's once-cell inline,
  computes and stores the value if it is not there, then reads the cell
  (next entry). The cell stores a boundary type; another value is wrapped
  in an `ElemBox`. The value is never freed. Program constants are forced
  at startup ([order.md](order.md)); toolchain constants and closed terms
  only on first use, as natively (Lean 4.34.0 makes a closed term a
  `lean_obj_once` cell, computed at its first read; the library's
  `initialize` constants run at startup, at their module's place, used or
  not; order.md).
- **Why:** Native CAFs and closed terms live for the whole run, evaluated
  once. `l2r_once_claim` makes a scheduler context that needs a constant
  another context is computing wait for it, as natively
  `lean_obj_once_cold` holds a lock: it was computed twice and the runtime
  aborted ("once slot set twice", 7edc0f5). `l2r_once_has` is the plain
  test (no wait), for the standard streams' mutable cells, which share
  the slots (`Lower/Externs.lean`).
- **Where:** `Lower/Conv.lean`: `cafAccessor`; `Lower/Code.lean`:
  `lowerDecl`; `runtime/prelude.rr`: `l2r_once_ready`, `l2r_once_claim`,
  `l2r_once_get`, `l2r_once_put`, `l2r_once_set`;
  `runtime/leanrt/src/once.rs`: `claim`.
- **Remove only if:** never (the storage may change, next entry).

### A read of a constant is one load

- **What:** The accessor is

  ```
  let r : u64 = if l2r_once_ready(k) { 0 }
                else { if l2r_once_claim(k) { 0 } else { l2r_once_put<T>(k, <f>_init()) } };
  l2r_once_get<T>(k)
  ```

  Each slot's word and set flag are also kept in `leanrt::once::FAST`
  and `FLAGS`, static tables at fixed addresses (2^18 words and 2^18
  bytes in `.bss`; untouched pages cost no memory). `l2r_once_ready(k)`
  loads word `k` and tests it against 0; when the word is 0 it loads flag
  `k` (a set slot whose value's bits are all 0: a `UInt64`, `Int64`,
  `USize`, `Float` or `UInt8` 0, `false`, a first constructor's index).
  `l2r_once_get` loads the same word (and flag) again, which LLVM merges
  with the first loads. The slot number is a literal at every read, so a
  read of a set constant, inlined, is one load from a constant address, a
  test and the increment; two loads and two tests when its word is 0; no
  call either way. The slow path (`claim`: the wait for another context,
  the computation, `put`, which moves the value's reference into the
  cell) rejoins before the read, so the read and its increment are on one
  straight path. A word is the value's bytes, the rest 0, as before the
  tables (`leanrt::once::word_of`). The streams'
  `has` uses the tables too. The clones of `Array`, `ByteArray`,
  `FloatArray` and `String` handles tell LLVM that the count was at least
  1 (`assert_unchecked`, `leanrt::drop::Vec`, `LStr`): a read from the table right after the constant's
  read (`give`, ownership.md "Reads give their reference up first, for a
  view") then folds the increment and the decrement away, so the table
  read has no count store at all, as a native persistent object. The
  computation `<f>_init` is kept out of rrc's MLIR inliner
  (`#[transform_anchor]`, `cafInits`, `anchoredFns`): it runs once, and
  inlined into the accessor (a literal table's run of pushes became small
  enough once a boxed immediate stopped allocating) it made the accessor
  too big to be inlined where the constant is read.
- **Why:** lean-zip's decoder (`goTreeFreeU`) read its length and
  distance tables (`lengthBase`, `distExtra`, …) through two calls each:
  `l2r_once_claim`, then `l2r_once_get`, whose bounds checks and panics
  kept it above LLVM's inlining threshold; inline, a read was seven loads
  (the vectors' lengths and pointers, the set flag, the value), five
  branches and two count stores. A profile of the decompression put 3.8%
  of its cycles in these calls. Now (lean-zip's survey IR, perf-const-reads):
  in the hot loop paths of lean-zip's codec functions, once-cell calls 17
  to 0 and loads of once-cell state 170 to 49 (one per read; each flag's
  load sits behind its word's test, in a block LLVM keeps cold); in the
  whole program, once-cell call sites 1068 to 433, all on slow paths, and
  inline loads of the slot record 7131 to 0 (its IR 9% smaller). A CRC
  table read in a loop is `ldr x0, [x28, #24]; cbnz x0, …` and nothing
  else (aarch64; `x28` holds the table's address for the whole loop).
  Native Lean reads a named constant as one global load and a closed term
  through `lean_obj_once` (two loads and a test). Reussir has no global
  variables; a table in the runtime gives the same one load. Leaving out
  the test after startup, where every program constant is set, would need
  a proof that the read runs after startup (code reachable from `main`
  only), and closed terms and toolchain constants are computed on first
  use anyway: the test is one well-predicted branch.
- **Where:** `Lower/Conv.lean`: `cafAccessor`; `Lower/Finish.lean`: `anchoredFns`; `runtime/prelude.rr`:
  `l2r_once_ready`, `l2r_once_get`, `l2r_once_put`, `l2r_once_set`,
  `l2r_cell_swap`; `runtime/leanrt/src/once.rs`: `FAST`, `FLAGS`,
  `FAST_SLOTS`, `has`, `ready`, `word_of`, `get_raw`, `rec_has`,
  `rec_get`, `set_raw`, `swap_raw`, `take_raw` (each keeps the tables in
  step with the record `SLOTS`); `runtime/leanrt/src/drop.rs` (`Vec::clone`),
  `string.rs`: the clones. Guard:
  `tests/runtime/const-read-check.sh` with `tests/runtime/RtConstReads.lean`
  (fails when a constant read in a loop is a call or reads `SLOTS`;
  review PCR-01: symbols read by their identifiers, whatever the
  mangling's prefix, and the check's own mutations named from the IR).
- **Remove only if:** Reussir gets globals that are cheaper still (none
  can be: one load), or Lean code runs on several threads at once (then
  the word's store must release and its load acquire, as natively; plan
  §5.12). A program with more than 2^18 slots reads the slots above
  through the record in line, as before the tables. The first version
  marked values smaller than a word with a bit of the word, so that only
  a 64-bit 0 had the word 0, and sent word-0 reads through two calls:
  slower than before for those constants, and a slot read at a wider type
  than it was stored at would have seen the mark (review PCR-02, PCR-03);
  the flag table replaced both.

### Cheap constants are recomputed, float literals folded

- **What:** A constant that only builds unboxed values from small
  literals, constructors and total scalar conversions, every `Nat`/`Int`
  among them small (a big one is a heap number, RV8N-01), is recomputed at
  each use (`cheap-consts`); a float literal (`Float.ofScientific` on
  literals) is evaluated by lean2rr and becomes `Float.ofBits` of its bit
  pattern (`float-lits`).
- **Why/Where:** see [../optional-passes.md](../optional-passes.md).
- **Remove only if:** they are optional passes: without them only speed
  changes.

### A constant's box is a once-cell too

- **What:** A constant boxed where boxing allocates (a `Float`, a
  `UInt64` from 2^63, ...) is boxed once: its box is the value of a
  once-cell `l2r_boxed_N` (`boxed-consts`), forced on first use, as
  native Lean's `_boxed_const_N` closed terms.
- **Why/Where:** see [../optional-passes.md](../optional-passes.md).
- **Remove only if:** the pass is off.

### A closed term used once, by another constant, is not cached

- **What:** A closed term referenced exactly once, from a constant (not
  from a function, not a root of the entry point), is evaluated where it is
  used instead of being kept in a once-cell. It still runs once, at the
  same point. Exception: in a program that creates tasks, a closed term
  whose type can hold a task (`holdsNoTask` is false: a function type,
  `lcAny`, a task, thunk, reference or promise, or an inductive with such
  a field at the type's arguments) keeps its once-cell, and so its walk
  for tasks ("A constant that may hold tasks waits for them", below).
- **Why:** Lean's `extractClosed` makes an `n`-element literal a chain of
  closed terms `_closed_k := push _closed_(k-1) e_k`; caching every step
  kept every intermediate array alive: memory quadratic in the literal's
  length (10000 elements: 1036 MB instead of 7 MB; adv2 N5, fbf37e8).
  The exception: natively every closed term is marked persistent at its
  first evaluation, which waits for its tasks and keeps them alive. An
  uncached term had no walk and was released after its one use: in
  `List.length (spawnOne 7)` and in `[mk 1, mk 2].length` the tasks were
  dropped and never ran (hunt2 startup; test `RtClosedChainTasks`).
  Literals of data (`List Nat`, `Array Float`, records of data) stay
  uncached.
- **Where:** `Emit/Program.lean`: `chainConsts`, `holdsNoTask`,
  `lowerProgram`; `LowerBase.lean`:
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

### A constant that may hold tasks waits for them

- **What:** When a constant whose type may hold a task is first computed,
  `l2r_persist_T` walks its value and waits for every task it reaches:
  through fields, arrays, the values of tasks, the values captured by
  function values, thunks (their computation or value, without forcing
  them), references (their value) and `Box` payloads. As natively, the
  walk is a loop over a work list (`L2RPersistW`: a variant per type that
  can hold a task, and one per array type for the elements left), in
  native's order: an object's fields are pushed in Lean's declaration
  order (`leanOrder`, whatever the record layout), the last on top, and an
  array is walked from its last element down. It has two passes: the
  first collects the unfinished tasks it reaches (`l2r_persist_collect_at`,
  not looking into them); the second walks again and, before it waits for
  a task, runs the collected tasks that come before it in the native
  workers' queue order (`l2r_task_run_before` over
  `leanrt::persist::before`: a higher priority first, then the earlier
  created). Only collected tasks run early, not other pending tasks of the
  program. The collected tasks are recorded by runtime entry and serial,
  without a reference, and `l2r_persist_rewalk` releases what the first
  pass kept, so a task the program drops during the second pass is
  deleted, not run (RV7L-07, test `RtPersistDropped`). A task is known by
  its identity for the runtime, its cell's address (`taskAddr`), so a task
  seen through another binder is collected rather than forced in the
  first pass (test `RtPersistConv`). It visits each cell
  (record, array, thunk or task, function value, `Box`, reference) once:
  the runtime keeps the set of addresses seen and, until the walk ends,
  what it read out of thunks, tasks and references, so no seen cell is
  freed and its address reused meanwhile. It is skipped when no task is unfinished
  (`l2r_task_settled`), always the case for constants evaluated at
  startup. The walks are generated at the end, once every variant of
  function types and `Box` is known; a type that cannot hold a task gets
  none. In a program that creates no task (`LowerCtx.createsTasks`) no
  constant is walked: with one type per inductive, nearly every type
  holds a `Box`, which could hold a task in a program that has some. A placeholder's never-forced task cell (`pending` with the `z`
  function value) is not a task (`l2r_persist_ph_T`): natively it is
  `box(0)`, which the walk skips (C01R-03). `Runtime.markPersistent`
  walks its argument the same way, then returns it: natively it calls
  `lean_mark_persistent` too.
- **Why:** As `lean_mark_persistent` at a closed term's first evaluation:
  a `Task.spawn` extracted as a closed term has finished once the term has
  been used (adv4 TK4-02, a599e0a; closures, thunks and boxes: 17ab235).
  The searches for task-holding types look at each type once: following
  every path took over ten minutes on polymorphic-recursion towers
  (1955043). The walk was a recursive function per type without a visited
  set: a 300000-link chain overflowed the 8 MB startup stack, even for an
  unused constant, and a 41-cell DAG was walked as a tree, 2^40 paths
  (round 7 RV7L-01, 42517bf; test `RtPersistWalk`). The order shows in
  the tasks' traces and panics: natively waiting only blocks
  (`wait_for`), and the workers run the term's tasks in queue order,
  whatever order the walk waits in, while here a pending task runs when it
  is waited for; walking first field first, then last field first, each
  ran some shapes in reverse (`(List.range 4).map (Task.spawn …)` ran 3 2
  1 0: round 7 RV7L-04, RV7L-06; test `RtPersistOrder`). The second pass
  keeps native's walk order because it reads references and thunks when
  it gets to them: a task that replaces the task a reference next to it
  holds has run by then, as natively. Native pushes a reference's value
  too (RV7L-05, test `RtPersistRef`). `Runtime.markPersistent` was the
  identity: the tasks its value held ran only when waited for, after the
  output that natively follows them (hunt2 startup; test
  `RtMarkPersistentWaits`).
- **Where:** `Lower/Conv.lean`: `persistCall`, `typeHoldsTask` (one
  search: `mayHoldTask` before the variants are final, `holdsTask`
  after), `persistFnName`, `cafAccessor`; `Lower/ExternCall.lean`:
  `lowerExternCall` (`Runtime.markPersistent`); `Lower/Finish.lean`: `holdsTask`,
  `persistListName`, `persistCell`, `PersistGen`, `genPersist`,
  `finishPersistFns`, `variantCount`; `runtime/prelude.rr`:
  `l2r_persist_begin`, `l2r_persist_seen`, `l2r_persist_keep`,
  `l2r_persist_collect_at`, `l2r_persist_rewalk`, `l2r_persist_before_at`,
  `l2r_persist_end`, `l2r_task_settled`; `Lower/Promises.lean`:
  `taskDispatchFns` (`l2r_task_run_before`);
  `runtime/leanrt/src/persist.rs`; `runtime/leanrt/src/task.rs`:
  `serial_base`, `persist_key`, `persist_hand`. Plan §5.14 (*Closed
  terms*), §10 (*Tasks*).
- **Remove only if:** never.

### What a constant's value holds is released at its last reference

- **What:** A constant's value, an `initialize` constant's included, is
  never freed (its once-cell holds it), but nothing in it is marked
  persistent: a value the program later takes out of it, or stores over
  (a reference an initializer made, set again by `main`), is released at
  its last reference, as any value. So a file handle that an initializer
  stores in an `IO.Ref` is closed when the program sets the reference to
  `none` and nothing else holds the handle: its buffered bytes are written
  then, and a `flock` it took is released. Natively the module
  initializers mark every constant's value persistent
  (`lean_mark_persistent`), a persistent object's count is never
  decremented, and that handle stays open until the process exits (glibc
  writes its buffer at the exit). Example: an initializer opens a file,
  writes "from-init" to the handle and stores the handle in an
  `IO.Ref (Option IO.FS.Handle)`; `main` sets the reference to `none`, then
  reads the file. Natively the read gives "", through lean2rr
  "from-init"; at the exit the file holds "from-init" in both (hunt
  HSG-02; plan §10, "Runtime").
- **Why:** lean2rr follows Lean's documentation of handles ("when the last
  reference to a file handle is dropped, the file is closed",
  `Init/System/IO.lean`). Persistence is not emulated: a value has no
  persistent mark, and `Runtime.markPersistent` returns its argument
  (`l2r_runtime_mark_persistent`).
- **Where:** `Lower/Conv.lean`: `cafAccessor`; `runtime/leanrt/src/fs.rs`:
  `FileHandle`'s drop; `runtime/prelude.rr`: `l2r_runtime_mark_persistent`.
- **Remove only if:** lean2rr marks values persistent.
