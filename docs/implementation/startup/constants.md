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
  for tasks ("A constant that may hold tasks waits for them, and the cells it
  reaches become persistent", below).
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

### A constant that may hold tasks waits for them, and the cells it reaches become persistent

- **What:** When a constant whose type may hold a task is first computed,
  `l2r_persist_T` walks its value and waits for every task it reaches:
  through fields, arrays, the values of tasks, the values captured by
  function values, thunks (their computation or value, without forcing
  them), references (their value), promises (their task, `result?`) and
  `Box` payloads. The walk also marks each cell it visits persistent
  (`l2r_persist_mark`, `leanrt::persist::mark`: the cell's `u32` count
  goes up by 2^30): a record, an array, a function value, a thunk or task,
  a reference, a promise. A persistent cell is never freed (its count
  never comes back to 1) and never unique, and no walk looks into it
  again: a walk that reaches it goes on with the rest, without a wait.
  The walk marks a cell when it reaches it, before it waits for the cell
  or looks into it. A `Box` is looked into where the walk meets it
  (`l2r_persist_x_LAny`), never pushed: a payload whose type can hold a
  task is pushed at that type (and marked when it is visited); any other
  payload (a file handle, a string, an array of scalars, a closure that
  no task can be in) is marked persistent there, without being looked
  into (`l2r_persist_box`, `leanrt::persist::mark_box`), so it keeps all
  it holds and a handle stays open; an immediate is nothing. The mark
  takes only the counted handle types (`leanrt::persist::Counted`:
  Reussir's records and enums, its `Rc`, leanrt's arrays and thunk or
  task cells); a box is marked through its word. The last value pushed is
  visited next: when it has the cell's own type (a list's tail, a tree's
  last child) the expansion calls itself on it, a tail call, and the step
  over an array of boxes loops over the elements that push nothing, so a
  `List Nat` or `Array Nat` constant makes no work-list cell. A count of
  2^31 (`drop::IMMORTAL`) or more is a nullary variant's dummy box for
  leanrt: a marked cell gets there at 2^30 references to it (8 GiB of
  pointers), an unmarked one at 2^31. The walk runs for a program constant at startup
  (forced there, [order.md](order.md)), for an `[init]` declaration's
  result right after its initializer (`initPutFn`), for a closed term or
  a toolchain constant at its first evaluation, and in
  `Runtime.markPersistent`. A walk at startup never waits: before `main`
  every task runs at once (Lean has no task manager yet), and
  `IO.Promise.new` is Lean's internal panic. `Runtime.markPersistent`
  also marks its argument itself persistent, whatever its type
  (`l2r_persist_box`, on the argument boxed, after the walk), so a
  marked file handle is never closed: its bytes are written by the exit
  flush. As natively, the walk is a loop over a work list
  (`L2RPersistW`: a variant per type that can hold a task, and one per
  array type for the elements left), in native's order: an object's
  fields are pushed in Lean's declaration order (`leanOrder`, whatever
  the record layout), the last on top, and an array is walked from its
  last element down. It waits for each task as it reaches it, in one
  pass ([../tasks/deferral.md](../tasks/deferral.md)). The walks are
  generated at the end, once every variant of function types and `Box`
  is known; a type that cannot hold a task gets none. In a program that
  creates no task (`LowerCtx.createsTasks`) no constant is walked: with
  one type per inductive, nearly every type holds a `Box`, which could
  hold a task in a program that has some. A placeholder's never-forced
  task cell (`pending` with the `z` function value) is not a task
  (`l2r_persist_ph_T`): natively it is `box(0)`, which the walk skips
  and does not mark (C01R-03). A promise is walked as its task
  (`l2r_promise_cell`), as native Lean pushes the promise's `m_result`:
  the walk waits until the promise is resolved, then walks its value (an
  `Option`). A closed term can reach a promise: through unsafe code
  (`unsafeBaseIO` makes one and starts its resolver, test
  `RtPersistClosedPromise`), or through a reference that a constant or
  an initializer made (persistent since startup, so the walk does not
  look into it: the example below). An initializer cannot make a
  promise.
  Example (native's rule, and lean2rr's): `initialize r : IO.Ref (Option
  (IO.Promise Nat)) ← IO.mkRef none` is walked after its initializer, so
  the reference is persistent while it holds `none`. `main` stores an
  unresolved promise in `r`, then reads a closed term `(r, "pair")`. The
  term's walk reaches `r`, which is persistent: it does not read `r`'s
  value, so it does not wait for the promise, and `main` goes on and
  resolves it.
- **Why:** As `lean_mark_persistent` at a closed term's first evaluation:
  a `Task.spawn` extracted as a closed term has finished once the term has
  been used (adv4 TK4-02, a599e0a; closures, thunks and boxes: 17ab235).
  The searches for task-holding types look at each type once: following
  every path took over ten minutes on polymorphic-recursion towers
  (1955043). The walk was a recursive function per type without a visited
  set: a 300000-link chain overflowed the 8 MB startup stack, even for an
  unused constant, and a 41-cell DAG was walked as a tree, 2^40 paths
  (round 7 RV7L-01, 42517bf; test `RtPersistWalk`). The order shows in
  the tasks' traces and panics: walking first field first, then last
  field first, each ran some shapes in reverse (`(List.range 4).map
  (Task.spawn …)` ran 3 2 1 0: round 7 RV7L-04, RV7L-06; test
  `RtPersistOrder`). A reference and a thunk are read when the walk gets
  to them: a task that replaces the task a reference next to it holds has
  run by then, as natively (RV7L-05, RV7L-07; tests `RtPersistRef`,
  `RtPersistDropped`). `Runtime.markPersistent` was the identity: the
  tasks its value held ran only when waited for, after the output that
  natively follows them (hunt2 startup; test `RtMarkPersistentWaits`).
  The walk did not look into a promise (`typeHoldsTask` was false for
  `LPromise`): `Runtime.markPersistent` of a value that reaches an
  unresolved promise returned at once, before the task that resolves it
  printed its line, and a closed term that made a promise did not wait
  for it (hunt HTSK2-02, review RV-02; tests `RtMarkPersistentPromise`,
  `RtPersistClosedPromise`). Nothing was remembered between walks (each
  walk had its own set of the cells it had seen), and the walk was
  skipped when no task was unfinished (always at startup): a closed term
  that reached a reference made by an initializer or a constant read the
  reference's current value and waited for the promise or task in it,
  which natively it does not see. A promise that `main` resolves only
  after it reads the term made the program hang (review RV-01 of
  HTSK2-02; tests `RtPersistInitRef`, `RtPersistConstRef`,
  `RtPersistConstRefPromise`, `RtPersistConstRefTask`); a second
  `Runtime.markPersistent` waited for what a reference and a thunk that a
  first one marked got later (test `RtMarkPersistentAgain`).
  `Runtime.markPersistent` made nothing persistent: a marked file handle
  was closed at its last reference (review RV-03 of HTSK2-02; test
  `RtMarkPersistentHandle`). The walk pushed every box, immediates
  included, as a work-list cell: constants `List.range 2000000` and
  `Array.range 2000000` read before any task exists made 6.00 million
  allocations and peaked at 98.8 MB, native 2.01 million and 117.7 MB,
  lean2rr without the mark 2.00 million and 70.3 MB; now 2.00 million and
  70.2 MB (review RM-02 of the persistent walk). It marked a box's
  payload only when the payload's type could hold a task: a file handle
  that a marked reference held directly was closed when the program set
  the reference (review RS-01; tests `RtPersistInitHandleDirect`,
  `RtMarkPersistentRefHandle`). The mark is in the cell, so no table is
  needed, a marked cell's address is never reused (the cell is never
  freed), and the hot paths (a reference's get and set, a thunk's force,
  a task's get, a promise's resolution) do not change; a later walk stops
  at what an earlier one marked, so a chain of closed terms that each add
  one cell to the one before is walked in time linear in its length.
- **Where:** `Lower/Conv.lean`: `persistCall`, `typeHoldsTask` (one
  search: `mayHoldTask` before the variants are final, `holdsTask`
  after), `persistFnName`, `cafAccessor`; `Lower/ExternCall.lean`:
  `lowerExternCall` (`Runtime.markPersistent`); `Emit/Startup.lean`:
  `initPutFn`; `Lower/Finish.lean`: `holdsTask`, `persistListName`,
  `persistCell`, `PersistGen`, `genPersist`, `finishPersistFns`,
  `variantCount`, `persistExpName`; `runtime/prelude.rr`:
  `l2r_persist_mark`, `l2r_persist_box`; `runtime/leanrt/src/persist.rs`:
  `Counted`, `mark`, `mark_box`, `PERSISTENT`. Plan §5.14 (*Closed
  terms*), §10 (*Tasks*, *Runtime*).
- **Remove only if:** never.

### What no walk reaches is released at its last reference

- **What:** A constant's value, an `initialize` constant's included, is
  never freed (its once-cell holds it). Persistent are: the cells the walk
  for tasks visits (the types that can hold a task, in a program that
  creates tasks), the payload of each box the walk meets (marked without
  being looked into), and `Runtime.markPersistent`'s argument (previous
  entry). A persistent cell never releases what it holds: a value of a
  type the walk does not look into (a string field, an array of scalars)
  stays alive while a persistent cell holds it. A value that no walk
  reached is released at its last reference, as any value, once the
  program takes it out of a reference or stores over it: in a program that
  creates no task, every value (nothing is walked) but
  `Runtime.markPersistent`'s argument; in a program that creates tasks,
  the value a reference or a thunk gets after the walk (natively not
  persistent either). Natively the module initializers mark every
  constant's value persistent (`lean_mark_persistent` visits every
  object), and a persistent object's count is never decremented. Example
  (hunt HSG-02): an initializer opens a file, writes "from-init" to the
  handle and stores the handle in an `IO.Ref (Option IO.FS.Handle)`;
  `main` sets the reference to `none`, then reads the file. Natively the
  handle stays open until the process exits (glibc writes its buffer at
  the exit), so the read gives "". In a program that creates no task
  lean2rr closes the handle when the reference is set (its last
  reference), so the read gives "from-init"; at the exit the file holds
  "from-init" in both (plan §10, "Runtime"). In a program that creates
  tasks the walk after the initializer marks the reference and the box
  it holds points to: the `some` cell (an `Option`'s field is a `Box`,
  which can hold a task there), or the handle itself when the reference
  holds it directly. So the handle stays open and the read gives "", as
  natively (tests `RtPersistInitHandle`, `RtPersistInitHandleDirect`).
  The same holds for a reference that `Runtime.markPersistent` marked: in
  a program with tasks the handle it held stays open when the program
  replaces it (test `RtMarkPersistentRefHandle`); in a program without
  tasks only the reference is marked, and the handle is released.
- **Why:** lean2rr follows Lean's documentation of handles ("when the last
  reference to a file handle is dropped, the file is closed",
  `Init/System/IO.lean`). The walk exists for tasks: it runs only in a
  program that creates them, so a program without tasks pays nothing.
  `Runtime.markPersistent` marks its argument whatever its type (review
  RV-03 of HTSK2-02, previous entry).
- **Where:** `Lower/Conv.lean`: `cafAccessor`, `mayHoldTask`;
  `Emit/Startup.lean`: `initPutFn`; `Lower/Finish.lean`: `genPersist`;
  `runtime/leanrt/src/fs.rs`: `FileHandle`'s drop;
  `runtime/leanrt/src/persist.rs`.
- **Remove only if:** the walk runs in every program.
