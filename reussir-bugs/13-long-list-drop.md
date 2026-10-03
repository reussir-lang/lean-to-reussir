# 13. Drop glue recurses once per cell of a long list

## Summary

**Kind:** missing feature. **Status:** patched (0013 and 0014; 0015 makes
0014's runtime cheaper). lean2rr's runtime needs 0014 to build, so it does
not build against upstream Reussir.

**Verdict: missing feature, not a bug.** Reussir's drop glue recurses, as
Rust's does, and nothing in Reussir promises bounded-depth frees (it
commits to deep tail recursion only,
`tests/integration/frontend/deep_value_tail_recursion.rr`). Native Lean
frees iteratively, and Lean programs drop long lists and deep trees, so
lean2rr needs it: 0013, 0014 and 0015 implement it locally (a new runtime
ABI, `reussir_rt::drop`, and Lean's release order).

When the last reference to a list goes away, Reussir's generated "drop
glue" releases the list's cells. For each cell it releases the members,
recursing into the tail, and only afterwards frees the cell. Because the
free comes after the recursive call, the call is not a tail call: freeing
a list of N cells needs N stack frames. Around 500,000 cells overflow an
8 MB stack; lean2rr's 1 GiB main thread overflows at about 33 million.
Native Lean frees iteratively.

- **0013** makes a release inside the drop glue call a new per-type
  function, `drop_and_free`. It frees the cell first, then releases the
  member that continues the chain as its very last action, a tail call
  that LLVM turns into a loop.
- **0014** (bug 13b) handles what 0013 leaves recursive: a value deep along
  a member the loop does not follow (a left-deep tree with fresh right
  children, a rose tree). Like Lean's `lean_del`, it keeps one stack of
  pending releases per thread in Reussir's runtime; inside drop glue, a
  record member whose count is 1 is pushed onto it instead of freed by a
  call. It replaces 0013's choice of chain members; the loop part remains.
  lean2rr's runtime frees its containers through the same stack.
- **0015** (bug 13b, runtime only) makes 0014's stack cheaper, with the
  same behaviour.

## Symptom and repro

Releasing a chain of cells at once takes one stack frame per cell. The
program needs no recursion of its own:

```lean
def main (args : List String) : IO Unit := do
  let l := List.replicate 40000000 7
  IO.println s!"{l.head?}"
```

**Repro.** Two files.

- [`repros/bug13-long-list-drop.rr`](repros/bug13-long-list-drop.rr)
  `SHAPE N` (plain Reussir, `main` on the 8 MB main thread) builds a chain
  of N cells, reads one field and drops the chain:

  ```
  enum L { Cons(u64, L), Nil }
  struct [shared] Box { v : u64 }
  enum Snoc { S(Snoc, Box), E }
  enum T { N(u64, T, T), Lf }
  fn mk(n : u64, acc : L) -> L { if n == 0 { acc } else { mk(n - 1, L::Cons{n, acc}) } }
  fn mks(i : u64, n : u64, acc : Snoc) -> Snoc { if i > n { acc } else { mks(i + 1, n, Snoc::S{acc, Box{v: i}}) } }
  fn lspine(i : u64, n : u64, acc : T) -> T { if i > n { acc } else { lspine(i + 1, n, T::N{i, acc, T::Lf{}}) } }
  fn hd(l : L, n : u64) -> u64 { match l { L::Cons(a, t) => { a * n }, L::Nil => { 0 } } }
  fn hs(s : Snoc) -> u64 { match s { Snoc::S(t, b) => { b.v }, Snoc::E => { 0 } } }
  fn root(t : T) -> u64 { match t { T::N(a, l, r) => { a }, T::Lf => { 0 } } }
  ... // main: shape 0 → say(hd(mk(n, L::Nil{}), n)); 1 → say(hs(mks(1, n, ...))); 2 → say(root(lspine(1, n, ...)))
  ```

  - SHAPE 0, a list whose recursive field is last: `Cons(u64, L)` (Lean's
    `List`);
  - SHAPE 1, a snoc list whose recursive field is first and a box is last:
    `S(Snoc, Box)`;
  - SHAPE 2, a left spine: `N(u64, T, T)` with the chain in the first `T`.
- [`repros/bug13-long-list-drop.lean`](repros/bug13-long-list-drop.lean)
  `CASE N` (through lean2rr, whose `main` runs on a thread with a 1 GiB
  stack): CASE 0 is `List.replicate N 7`, CASE 1 a snoc list
  `SnocS.snoc : SnocS → String → SnocS`.

**Command.** `rrc bug13-long-list-drop.rr` with lean2rr's flags, then
`./bug13 0 1000000`; `scripts/l2r.py` on the Lean file, then
`./prog 0 40000000`.

**Expected.** The plain repro prints N; the Lean repro prints `(some 7)`
(CASE 0) or `0` (CASE 1), like native Lean.

**Actual on ef922049.**

- Plain, 8 MB stack: `thread 'main' has overflowed its stack`, `fatal
  runtime error: stack overflow, aborting` (SIGABRT). A list (SHAPE 0)
  takes 16 bytes of stack per cell and overflows above about 524,000
  cells; the snoc list and the left spine take 32 bytes per cell and
  overflow above about 261,000 cells.
- lean2rr, 1 GiB stack: `Stack overflow detected. Aborting.` (exit 134;
  the line printed before is lost). Both cases take 32 bytes per cell:
  33,437,500 cells work, 33,906,250 abort.
- At 10 million elements (lean2rr, best of 5, max RSS), with the patch
  versions for comparison:

  | | `List.replicate` | snoc list |
  |---|---|---|
  | native Lean | 0.08 s, 313 MiB | 0.08 s, 313 MiB |
  | ef922049 | 0.18 s, 617 MiB | 0.17 s, 541 MiB |
  | 0013, first version | 0.08 s, 312 MiB | 0.16 s, 541 MiB |
  | 0013, extended (the patch file) | 0.06 s, 312 MiB | 0.07 s, 236 MiB |

  The extra 300 MiB on ef922049 is the stack: 10 million frames of 32
  bytes stay resident.
- `run.sh` printed, for each plain shape,
  `bug 13   REPRODUCES  list, 1M cells, 8 MB stack: overflowed its stack (SIGABRT)`
  (and `snoc`, `lspine`), and for the Lean repro
  `bug 13   REPRODUCES  lean2rr List.replicate, 40M cells, 1 GiB stack: Stack overflow (SIGABRT)`
  (and `snoc`).

## Cause

The drop function of a cell (`drop_in_place`, outlined by
`lib/Conversion/AcquireDropExpansion/AcquireDropExpansion.cpp`) releases
the cell's members, and the release of an rc member expands
(`RcDecrementExpansion`) to "count == 1 → call the member's drop function,
take the cell as a token"; the token is freed after that call. So the free
of each cell follows the recursive call on its tail: not a tail call.

In detail: for a named record type `T`, `createDtorIfNotExists`
(`lib/IR/ReussirOps.cpp`) creates `drop_in_place::<T>(ref<T>)`. It drops
the *contents* of a cell (its body is a single `ref.drop`); the caller
frees the cell. `AcquireDropExpansion` expands `ref.drop`: a variant
becomes a dispatch on the tag, and a compound becomes one drop per managed
member. An `rc` member becomes, in `rewriteDropRc`, "load the member;
`rc.dec` it". That `rc.dec` produces a token, like any release. In its
second phase (expand decrements, outline record drops) the pass expands
that `rc.dec` through the same pattern as `RcDecrementExpansion`:
"count == 1 → drop the member's contents (a call to `drop_in_place` of the
member's type) and take the member's cell as a token; else count − 1". No
construction can use a token inside drop glue, so TokenReuse frees it, in
the unique branch after the call.

For `L` the result is, in effect:

```c
void drop_in_place_L(L *cell) {            // releases the contents only
  if (cell->tag == Cons) {
    L *tail = cell->cons.tail;
    if (tail->count == 1) {
      drop_in_place_L(tail);               // recursion ...
      free(tail);                          // ... then more work: not a tail call
    } else {
      tail->count -= 1;
    }
  }
}
```

Each cell's free waits for the release of the whole rest of the list, so
the stack grows by one frame per cell. Releases outside the glue (in user
functions) must keep this shape, because their token may be reused by a
later construction.

## lean2rr

lean2rr cannot avoid releasing long lists or other chains of records,
since every Lean program that builds one drops it eventually. Its runtime
frees its own containers (arrays, references, thunks, tasks) through
0014's stack (`leanrt::drop` uses `reussir_rt::drop`), so it needs 0014 to
build.

## Patch

Three patches, in this order: 0013, then 0014 (which rewrites part of
0013's code), then 0015 (which rewrites 0014's runtime). The full order is
the [apply list](README.md#applying-the-patches).

### 0013: release chains of cells in a loop

Patch file
[`patches/0013-l2r-local-bug-13-release-chains-of-cells-in-a-loop-in-the-drop-glue.patch`](patches/0013-l2r-local-bug-13-release-chains-of-cells-in-a-loop-in-the-drop-glue.patch)
(`l2r-local` commit `2f4d25e1`). The file holds the *extended* version,
which review round 3 checked.

**Mark the glue** (`ReussirOps.h`, `ReussirOps.cpp`). The new attribute
`kDropGlueAttr = "reussir.drop_glue"` is set on every `drop_in_place`, and
later on every `drop_and_free`. Inside these functions no token can be
reused.

**Release differently inside the glue** (`rewriteDropRc`). If the enclosing
function has `kDropGlueAttr` and the member type
`releasesThroughDropAndFree`, the member is loaded and `emitGlueRelease`
emits:

```
if (count == 1) call drop_and_free::<T>(member)   // likely
else            rc.set(member, count - 1)
```

`releasesThroughDropAndFree` holds for plain shared boxes (non-atomic,
non-regional) of a named, complete record that has at least one chain
member in some arm. Releases outside drop functions, whose cells may be
reused, are unchanged.

**`drop_and_free::<T>(cell)`** (`getOrCreateDropAndFree`, named
`_RINvNvC4core9intrinsic13drop_and_free<T>E`, `linkonce_odr`, private). It
is only called on a cell whose count was read as 1. Its body dispatches on
the arm and, per arm (`emitCellRelease`):

1. returns at once for a nullary arm of a taggable type under the
   special-pointer-tag scheme: an immediate, a static dummy whose count may
   have wrapped to 1 ([bug 6](06-static-count-wrap.md)), so nothing to
   free;
2. loads the chain members;
3. drops every other managed member (`ref.drop`, the ordinary glue);
4. frees the cell with its arm's size (`getVariantArmAllocSize` for a
   fused variant header);
5. releases the chain members (`emitChainRelease`).

**Chain members** (`chainMembers`) are the plain shared record boxes of the
arm whose type can hold the cell's type again (`reaches`: the cell's
recursive group, through records, boxes and nullable links), wherever they
sit in the cell. If there is none, it is the arm's last managed member, if
that is such a box. So `L::Cons`'s chain is its tail, `Snoc::S`'s is its
first member, `T::N`'s is both children, and a mutually recursive pair
follows each other.

**`emitChainRelease(links)`.** With one link, it is `emitGlueRelease`, the
final operation of the function: a tail call. With several, it first reads
all the counts and decrements the links whose count is not 1. Of the links
whose count is 1 (about to be freed), it releases all but the last one
first, then the last one as the final operation (the tail call), so the
loop follows whichever member carries the chain:

```
if (unique[i] && any later unique) drop_and_free(links[i])   // for each i
if (unique[m-1]) drop_and_free(links[m-1])                   // tail calls
else if (unique[m-2]) drop_and_free(links[m-2]) ...
```

In effect, for `L`:

```c
void drop_and_free_L(L *cell) {            // cell->count was 1
  if (cell is the Nil immediate) return;
  L *tail = cell->cons.tail;
  free(cell);
  if (tail->count == 1) drop_and_free_L(tail);   // tail call → loop
  else tail->count -= 1;
}
```

The current build produces this LLVM IR for `L`, compiled at `-O
aggressive` (abbreviated: the GEPs are written inline and the immediate
check of the decrement is cut). After 0014 the function is called
`drop_and_free_in_drain`; for this type 0014 changes nothing else.

```llvm
define linkonce_odr void @_RINvNvC4core9intrinsic22drop_and_free_in_drainC1LE(ptr noundef nonnull %0) {
  br label %tailrecurse
tailrecurse:
  %.tr = phi ptr [ %0, %1 ], [ %7, %5 ]
  %3 = load i32, ptr (gep %.tr, 4)                ; the tag
  br i1 (trunc %3 to i1), label %.loopexit, label %5     ; Nil: done
5:
  %7 = load ptr, ptr (gep %.tr, 16)               ; the tail
  tail call void @__reussir_deallocate(ptr nonnull %.tr, i64 8, i64 24)
  %8 = load i32, ptr %7                           ; the tail's count
  br i1 (icmp eq i32 %8, 1), label %tailrecurse, label %10
  ...                                             ; else decrement (if not an immediate)
}
```

**Why it is correct.**

- `drop_and_free` runs only on a cell whose count was read as 1, inside
  glue, where nothing can reuse a token. Freeing the cell before releasing
  its chain members is safe, because the members were loaded first.
- A link whose count is 1 is referenced only by this cell, so releasing
  one link cannot reach another, and the counts read up front stay valid.
- The same value held twice by one cell is handled by the sequential
  decrements. With `N{l, l}`, the first decrement takes the count from 2
  to 1, and the second sees 1 and frees it (review round 3).
- Releases outside the glue are unchanged, as are atomic and regional
  boxes.

**Limits.** At `-O none` LLVM does not turn the tail call into a loop, so
every chain still overflows there. Of a cell's chain members being freed,
only the last is a loop. The others are released by ordinary (recursive)
calls, so a tree deep along a child that is not the last still recurses
(0014 handles that case). Chains through `Nullable` links or closures, and
atomic (`Arc`) spines, still recurse (review round 4, finding R4-5).

**History.** The first version, reviewed in round 2: inside drop
functions, a release whose count is 1 calls `drop_and_free::<T>`, which
drops the cell's other members, frees the cell, and releases the cell's
*last managed member* as its last operation, a tail call that LLVM turns
into a loop. It covered chains through the last managed member: Lean's
`List`, a list whose head is a `Nat` holding a box, mutual recursion
through two types, a right spine. A tree still recursed along its other
children. With it, `List.replicate 40000000` took 0.25 s (native 0.37 s)
with native memory. It did not cover the snoc list or the left spine:
SHAPE 1 and 2 and CASE 1 still overflowed (round 2, finding R2-6). The
extension (chain members of the recursive group, wherever they sit, the
last about to be freed released as the tail call) is what the patch file
contains. A build of it passes all three plain shapes at 1M cells and both
Lean cases at 40M.

**Verification.**

- Review round 2 (first version): 40M-cell chains on an 8 MB stack (list,
  a list whose `[value]` head holds a box, mutual recursion, a right spine)
  were fine at `-O aggressive` and `default`, ASan was clean at 1M cells,
  and the Lean `LongDrop` cases passed. It also measured binarytrees +3.4%
  on one core type (R2-5).
- Round 3 (extended version): all chain shapes, including the left spine
  and `Snoc(Snoc, Box)`, at 40M cells. ASan with leak detection was clean
  on DAGs (each child held twice), two long chains in one tree, chains
  through value records, a mutual group through a struct, and a chain
  whose middle cell is kept alive elsewhere. Forced-wrap tests of bug 6
  passed, and the Lean `LongDrop` cases matched native. Binarytrees was
  within noise (+2% on one core type) and Deriv 5% faster (R3-1).
- `run.sh` on the patched build: all three plain shapes print
  `bug 13   FIXED       list, 1M cells, 8 MB stack: prints 1000000` (and
  `snoc`, `lspine`). Both Lean cases are FIXED at 40M cells from 0013
  (extended) on.

**Effect on lean2rr.** Releasing a long list (or any chain of cells) runs
in a loop, not one stack frame per cell, at native speed and memory or
better (table above).

### 0014: a stack of pending releases (bug 13b)

Patch file
[`patches/0014-l2r-local-bug-13b-free-cells-deep-through-records-with-a-stack-of-pending-releases.patch`](patches/0014-l2r-local-bug-13b-free-cells-deep-through-records-with-a-stack-of-pending-releases.patch)
(`l2r-local` commit `824e3629`; it applies on top of 0013 and the patches
before it in the apply list).

**What 0013 leaves recursive.** A cell with two chain members being freed
loops along the last one only and recurses into the other. With 0013,
`drop_and_free::<T>` for `T::Node(l, v, r)` treats both children as chain
members (both can hold a `T`), and `emitChainRelease` does this:

```c
void drop_and_free_T(T *cell) {
  T *l = cell->l, *r = cell->r;
  free(cell);
  // decrement the children whose count is not 1, then:
  if (l->count == 1 && r->count == 1) drop_and_free_T(l);   // NOT a tail call
  if (r->count == 1)      drop_and_free_T(r);                // tail call
  else if (l->count == 1) drop_and_free_T(l);                // tail call
}
```

So a binary tree deep along its left child whose right children are fresh
nodes, or a rose tree in uniform code (`List` cells whose head holds the
deep tree and whose tail a fresh node), overflows an 8 MB stack at 10⁶
levels. In a left-deep tree every right child is a fresh node with count 1,
so the first, non-tail call runs at every level: one frame per level along
`l`. Choosing a different "last" member does not help, since the deep side
can be either: any scheme that frees one member per call recurses on some
shape. Native Lean pushes every child that is freed onto a stack of
objects to free (`lean_del_core`'s to-do list). lean2rr's runtime cannot
reach this recursion itself: records release records directly in the
glue.

The bug 13 repros in `repros/` are chains that 0013 already fixes. The 13b
case is lean2rr's runtime test `tests/runtime/RtDropGlue.lean`, run with
`LEAN_STACK_SIZE_KB=8192`:

```lean
inductive T2 | leaf | node (l : T2) (v : Nat) (r : T2)
inductive Rose (α : Type) | node (v : α) (kids : List (Rose α))
structure G where
  α : Type
  x : α

@[noinline] def leftDeep (n : Nat) : T2 := Id.run do
  let mut acc : T2 := .leaf
  for i in [0:n] do acc := .node acc i (.node .leaf i .leaf)
  return acc
@[noinline] def top : T2 → Nat | .leaf => 0 | .node _ v _ => v
@[noinline] def mkRoseAny {α : Type} (x : α) (n : Nat) : Rose α := Id.run do
  let mut acc : Rose α := .node x []
  for _ in [0:n] do acc := .node x [acc, .node x []]
  return acc
@[noinline] def roseU (g : G) (n : Nat) : Nat := match mkRoseAny g.x n with | .node _ ks => ks.length

def main : IO Unit := do
  IO.println s!"left spine {top (leftDeep 1000000)}"
  IO.println s!"rose {roseU ⟨Nat, 3⟩ 1000000}"
```

The rose tree is used through `G`, so it lives in lean2rr's uniform code.
Its `List` cells hold the deep tree in their head and a fresh node in their
tail. The patch adds the same two shapes to Reussir's lit test
`tests/integration/frontend/drop_long_list.rr`:

```
enum T { Node(T, u64, T), Leaf }
enum R { Rn(u64, RL) }
enum RL { Rc(R, RL), Rnil }
fn lfresh(n : u64, acc : T) -> T { if n == 0 { acc } else { lfresh(n - 1, T::Node { acc, n, T::Node { T::Leaf {}, n, T::Leaf {} } }) } }
fn rose(n : u64, acc : R) -> R { if n == 0 { acc } else { rose(n - 1, R::Rn { n, RL::Rc { acc, RL::Rc { R::Rn { n, RL::Rnil {} }, RL::Rnil {} } } }) } }
```

- Expected: `left spine 999999`, `rose 2`, as natively.
- Actual with 0013 alone: both trees overflow an 8 MB stack at 10^6 levels
  (`RtDropGlue` was marked as an expected failure until 0014). On
  ef922049 every deep shape overflows.

**The fix: runtime** (`crates/reussir-rt/src/drop.rs`, new).

- One stack of work per thread: `PENDING: RefCell<Vec<Work>>`, a
  `DRAINING` flag, and a table `RELEASES` of at most 255 release
  functions. A `Work` is either `Run { release, head, n }` (n deferred
  cells; the last one pushed is `head`, and `release` is its function) or
  `Step(p, step)` (incremental work from a host runtime).
- `__reussir_drop_defer(cell, release)` and
  `__reussir_drop_defer_wide(cell, release)` (C ABI) push a cell whose
  count was read as 1 and which nothing else references.
- `__reussir_drop_drain()` pops and runs work, last pushed first, until
  none is left, including whatever the releases push. A drain started
  while one runs returns at once, so the outermost drain does all the
  work. At the end it empties the table and shrinks the vector back to 64
  entries (the stack shrinks back after a large drain).
- For a host runtime that wants one worklist with the glue: `active()`,
  `depth()`, `defer_step(p, step)`, `run_step(p, step)`. lean2rr's
  `leanrt::drop` uses these.

**No memory per pending cell.** Like Lean's list, the stack takes no memory
per pending cell. A deferred cell is dead: its count is known to be 1, and
only the pending stack refers to it. Consecutive deferred cells form one
entry: `link()` stores, in the cell's own 8-byte header, the link to the
cell pushed before it in the same run:

```
header of a "wide" box:  word 0 = u32 count       word 1 = u32 tag (< 2^16) or padding
while linked:            word 0 bits 0-7   = idx
                         word 0 bits 8-31  = offset bits 0-23
                         word 1 bits 0-15  = tag (kept)
                         word 1 bits 16-31 = offset bits 24-39
offset = (previous cell - this cell) / 8, signed 40 bits (±2^42 bytes)
idx    = 0xff ("SAME": the previous cell has this cell's release function),
         or an index into the per-thread table RELEASES
```

Each link holds the offset to the previous cell (40 bits) and its release
function: the same as this cell's, or an index in the small per-thread
table, which is emptied with the stack. A fused variant's tag is kept.
`unlink()` reads the link back and restores the header (count 1, upper half
of the tag word 0) before the cell's release function runs. A cell starts a
new run, a 24-byte `Work` entry, instead of linking when:

- it was deferred through the narrow entry point (no spare header bits);
- it is an immediate's dummy (nonzero top byte), which is never written;
- it is not 8-aligned, or farther than 2^42 bytes from the previous cell;
- its predecessor's function is new and the table is full.

**The fix: compiler.**

- **New op `reussir.rc.defer_release(%cell) release(@fn)`**
  (`ReussirOps.td`). `BasicOpsLowering.cpp` lowers it to a call of
  `__reussir_drop_defer_wide` when the box has a wide header (a fused
  variant header with at most 2^16 arms, or a compound record with ABI
  alignment ≥ 8, whose bytes 4..8 are padding), and of
  `__reussir_drop_defer` otherwise.
- **`AcquireDropExpansion.cpp`** replaces 0013's chain-member logic
  (`reaches`, `chainMembers`, `emitChainRelease`):
  - `isDeferrable(type)`: a plain shared (non-atomic, non-regional) box of
    a named record.
  - `hasManagedMembers(record)`: some arm has a member that is not
    trivially copyable. A record without one is a *leaf*. A leaf (a box of
    a record with no managed members) is freed at once and never deferred:
    it cannot recurse and has no effect to order.
  - `emitDeferredRelease(v)`: `count == 1 → rc.defer_release(v,
    drop_and_free_in_drain::<T>)`, else `count − 1`. A leaf goes to
    `emitLastRelease` instead.
  - `emitLastRelease(v)`: `count == 1 → call drop_and_free_in_drain::<T>(v)`
    (a tail call when it is the function's last action), else `count − 1`.
  - `emitCellRelease` (one arm of `drop_and_free`): it picks the *last*
    non-leaf deferrable member as the loop member and loads it. Other
    deferrable members go through `emitDeferredRelease`, and other managed
    members (arrays, closures, FFI objects, ...) through `ref.drop` as
    before. Then it frees the cell, and finally calls
    `emitLastRelease(last)`. So `drop_and_free` still releases its cell's
    last record member by a tail call, and a chain stays a loop with no
    runtime call per cell; when the chain ends, the drain pops the next
    pending member.
  - In `rewriteDropRc`, every deferrable member released inside glue goes
    through `emitDeferredRelease`.
  - `drop_and_free` is renamed `drop_and_free_in_drain`. Its contract
    changed (it must run inside a drain), so it must not merge, as a
    `linkonce_odr` definition, with a `drop_and_free` from an rrc without
    the stack. It also no longer claims `nocallback`, since its releases
    reach the module again (FFI release hooks, the drain).
- **`ReussirOps.cpp`, `createDtorIfNotExists`:** a non-atomic
  `drop_in_place` drops the contents and then calls
  `__reussir_drop_drain()` (it empties the stack before it returns),
  without `nocallback`. Atomic dtors are unchanged and never defer.
- Reussir's lit test `frontend/drop_long_list.rr` gains the left-deep tree
  and the rose tree (above).

Here is `drop_and_free_in_drain::<T>` for the bug 13 repro's
`T = N(u64, T, T)`, from the current build (abbreviated LLVM IR, `-O
aggressive`). The left child is deferred, and the right child is the
loop:

```llvm
tailrecurse:
  %.tr = phi ptr [ %0, %1 ], [ %7, %16 ]
  ... tag check: Leaf → return ...
  %7 = load ptr, ptr (gep %.tr, 24)               ; right child: the loop member
  %9 = load ptr, ptr (gep %.tr, 16)               ; left child
  br i1 (icmp eq (load i32 %9), 1), label %12, label %13
12:
  tail call void @__reussir_drop_defer_wide(ptr %9, ptr @..drop_and_free_in_drainC1TE)
13:   ; else: decrement the left child unless it is an immediate
16:
  tail call void @__reussir_deallocate(ptr %.tr, i64 8, i64 32)
  br i1 (icmp eq (load i32 %7), 1), label %tailrecurse, label %19
```

Freeing `leftDeep`: the first cell defers its left child, frees itself,
and loops into its right child, a fresh leaf-level node that ends quickly.
The drain then pops the left child, which does the same. The native stack
stays at a constant depth, and at most a few cells are pending at a time.

**Why it is correct** (as checked in review round 4):

- Cells are deferred only inside glue: in `drop_in_place`, which drains
  before returning, and in `drop_and_free_in_drain`, which runs only from
  a drain. So outside the glue the stack is always empty. Nothing is
  pending when user code resumes or at thread exit.
- A deferred cell has count 1, and the reference being dropped is its only
  one. Nothing can reach it before the drain pops it. Its count is not
  decremented to 0, so no reuse token can see it. Tokens are never reused
  inside glue anyway.
- `link()` writes only into a deferred cell's own header, never into an
  immediate's dummy (top-byte check) or an unaligned cell. The header is
  restored before the cell's release function runs.
- Nested drains (a `drop_in_place` reached from a release, or from an FFI
  hook) return at once. A panic inside a drain aborts (`extern "C"`).
- Bug 6: under TBI a wrapped dummy count of 1 is deferred to
  `drop_and_free_in_drain`, whose dispatch takes the nullary arm and frees
  nothing.

**Release order.** Members are pushed in field order and popped last
first, and the loop member is the last record member, which `lean_del`
(`lean_del_core`) also takes first. With one stack, the order of
observable releases (handles closed, promises resolved) is therefore
Lean's in every free that starts at a container, and mostly below the
first cell of a free that starts at a record.

*Order that still differs.* That first cell is released by the inline code
Reussir emits in the user's function (`RcDecrementExpansion`, the unique
path), outside any drain: its fields in field order, each completely
before the next. Native Lean does the same where its code knows the
constructor of the value it drops (`lean_dec_ref_known`); elsewhere
(`lean_dec`, then `lean_del_core`) it goes last first. lean2rr's release
points are not Lean's (where Lean borrows a parameter and drops the value
in the caller, lean2rr's function takes it and releases it as it
destructures it), so a value dropped by itself can come out in the other
order: a list of handles `L0 … L7` is closed `L0 L7 L6 … L1` (natively
`L7 … L0`; before 0014 `L0 … L7`), and a tree of handles closes its left
subtree, then its handle, then its right subtree (natively the reverse;
each subtree is in Lean's order). No fixed member order in Reussir matches
both kinds of site. Both reversals were tried with the shared stack:

- Reversing the members in the drop glue changes nothing at the first
  cell, which is not glue. Below it, it breaks the order everywhere (in
  arrays, trees and lists): the glue's order is already `lean_del_core`'s.
  It pushes members in field order and they are popped last first, and the
  tail call is the last member, which `lean_del_core` pops first.
- Reversing them in user code's inline releases matches lists and trees
  dropped by themselves. But it breaks the cases where Lean uses field
  order (a structure of two handles dropped after a call: natively `a b`),
  and it breaks the order inside containers. The release code that
  leanrt's containers call for their Reussir elements (`_ffi_release`) is
  user code of this kind, and it runs inside a drain, where each member is
  pushed instead of finished.

One case below the first cell also differs. A cell that the first cell
holds is released by its `drop_in_place` outside any drain. That function
pushes record members, but a container member's free (an array, a
reference, a thunk) runs at once and empties the stack. So a structure
`{a : Array Handle, l : List Handle}` in a list dropped by itself closes
`A1 A0 L1 L0` (natively `L1 L0 A1 A0`). Running such a `drop_in_place` as
a drain would take a runtime call more on each one. Not done (plan §10).

**Verification.** The patch went through review round 4 and two revisions
(rounds 4b, 4c).

- **Round 4** (first version, one 24-byte stack entry per pending cell)
  found no use after free, leak, wrong result or crash. It did find a
  memory regression (R4-1). Freeing a list whose elements are boxes keeps
  every element pending until the spine is freed, so that took 24 extra
  bytes per element, more at the peak: 10^7 pairs peaked at 1.14 GB
  against 633 MB, and the thread kept the memory after the drop. It also
  asked for the rename (R4-4) and for `nocallback` to go (R4-3).
- **Round 4b** (a first fix: links through the 32-bit count only, with a
  ±64 MB window, and a 256-entry table never emptied) fixed R4-1 for lists
  in allocation order. The regression came back for elements more than
  64 MB apart (a sorted list: 1.00 GB against 555 MB; R4b-1) and after 256
  release functions on a thread (R4b-2).
- **Round 4c** (the patch file: 40-bit offsets in the whole header word,
  the SAME index, the table emptied after each outermost drain, the leaf
  rule) found nothing beyond a negligible case. More than 255 distinct
  predecessor functions within one drain fall back to entries (an
  artificial test: +13% memory). Memory equals 0013's on every test
  (MemDrop2, MemSort, MemScat, memd). Its runtime fuzzer checks the release
  order against a LIFO model, the restored counts and canaries, the
  release function, completeness, and each link decision. It ran 3000
  seeds × 8 threads (4.29M links) and 400 seeds with 300 functions, plus a
  far test at ±2^42 bytes and 700 seeds under ASan, with no failure.
- In all of these rounds: the chain shapes at 40M cells and deeper shapes
  at 10^6 on an 8 MB stack, ASan with leak detection, forced-wrap tests of
  bug 6, differential fuzzing, the lean2rr runtime suite (119/119,
  including `RtDropGlue` and `RtDropOrderRec`), the corpus oracle check
  (54/54), and Reussir's benchmark suite.
- `run.sh` on the patched build prints FIXED for the three plain bug 13
  shapes (as with 0013). The 13b shapes are checked by `RtDropGlue` and the
  lit test.

**Effect on lean2rr.**

- With 0014, every value deep through records is freed at a bounded depth.
  At an 8 MB stack, `RtDropGlue` passes (both trees at 10^6 levels), the
  left-deep tree is freed at 10^7 levels, and the list, snoc list and
  spine shapes of the review rounds at 4·10^7 cells. ASan with leak
  detection is clean.
- lean2rr's runtime frees its containers (`leanrt::drop`: arrays,
  references, thunks, tasks) through the same stack
  (`reussir_rt::drop::{active, defer_step, run_step, depth}`), so one free
  has one worklist through records and containers alike; the runtime
  therefore needs 0014 to build. Two stacks did not compose: each is
  last-in first-out on its own, and with 0014 and the runtime's own stack,
  handles in lists or trees inside an array no longer came out in Lean's
  order (lists `A0 … A3` and `B0 B1 B2` in one array: `B1 B2 B0 A1 A2 A3
  A0`, natively `B2 B1 B0 A3 A2 A1 A0`; test `RtDropOrderRec`). With one
  stack it matches native.
- Cost: about 10% on allocation-heavy programs (Deriv 3.70 → 4.09 s,
  MonadicInterp 1.73 → 1.89 s), most of it recovered by 0015.
- Still recursive (review round 4, R4-5): chains through `Nullable` links
  or closures, atomic spines (lean2rr emits none), and everything at
  `-O none` (no tail-call optimization).

### 0015: a cheaper pending stack, same behaviour (bug 13b, runtime)

Patch file
[`patches/0015-l2r-local-bug-13b-runtime-cheaper-pending-stack-same.patch`](patches/0015-l2r-local-bug-13b-runtime-cheaper-pending-stack-same.patch)
(`l2r-local` commit `ef0235b9`; it applies on top of 0014). No compiler
code changes.

**Symptom: speed only.** 0014's drop glue calls the runtime's pending-stack
functions for every record cell it frees, and drains the stack at the end
of every `drop_in_place`. Its pending stack cost allocation-heavy programs
about 10% (wall time, against the same lean2rr on Reussir without 0014's
code generation):

| | without 0014 | with 0014 |
|---|---|---|
| Deriv (classic benchmark) | 3.70 s | 4.09 s |
| MonadicInterp | 1.73 s | 1.89 s |

The patch message measures user cycles (`perf stat`, minimum of 4
interleaved runs, over the same lean2rr without 0014's code generation):
deriv +17.5%, monadic-interp +20.2%, cfold +5.3%; binarytrees and rbtree
unchanged. The two measurements use different metrics (wall time against
user cycles), which explains the different percentages.

**Cause.** 0014's runtime state:

```rust
thread_local! {
    static PENDING: RefCell<Vec<Work>> = const { RefCell::new(Vec::new()) };
    static DRAINING: Cell<bool> = const { Cell::new(false) };
    static RELEASES: RefCell<Vec<Release>> = const { RefCell::new(Vec::new()) };
}
```

Every deferral did `PENDING.with(|pending| pending.borrow_mut() ...)`, and
every drain did `DRAINING.with(...)` and then, in its loop,
`PENDING.with(...)` per popped cell, `RELEASES.with(...)` to clear the
table, and a `shrink_to` check. Per the patch message, the costs were:

- `PENDING` and `RELEASES` have destructors (they are `Vec`s), so every
  access checked the thread-local's destructor registration;
- every access went through a `RefCell` borrow flag;
- every drain ran the whole function with its prologue, even with nothing
  pending, which is the case after most frees;
- every deferral and pop loaded the vector's length and buffer before the
  top entry.

Part of the remaining cost is inherent to deferring: a popped cell's
header is a cache miss that recursion did not have, and the generated glue
makes calls, which only a change of the code generator would remove.

**The fix.** Everything is in `drop.rs`, plus a new test module
`drop/tests.rs`.

*One state, no destructor.*

```rust
#[repr(C)]
struct State {
    n: Cell<u32>,                 // the run on top, if n != 0 ...
    draining: Cell<bool>,
    head: Cell<*mut u8>,          // ... its last pushed cell
    release: Cell<Release>,       // ... and that cell's release function
    len: Cell<usize>,             // the entries below: a Vec<Work> by raw parts
    ptr: Cell<NonNull<Work>>,
    cap: Cell<usize>,
    known: Cell<usize>,           // entries of `releases` in use
    releases: [Cell<Release>; SAME as usize],   // the table, inline (255)
}
thread_local! {
    static STATE: State = const { ... };
    static GUARD: Guard = const { Guard };      // frees the vector at thread exit
}
```

`state()` turns the thread-local into a `&'static State`. That is sound
because `State` has no destructor and is not `Sync`, so the reference
cannot leave the thread. With no destructor and only `Cell`s, an access is
just the thread-local's address: no registration check and no borrow flag.
The vector's buffer, which is kept between drops, is freed at thread exit
by `GUARD`. `GUARD` is registered when the first buffer is allocated (in
`grow`).

*The top run lives in the state.* The invariant (doc comment of `State`):
the top entry is a run exactly when `n != 0`, and when `n == 0` the
vector's last entry, if any, is a step. A deferral that links to the top
run, and a pop from it, touch only the state's first cache line.
`try_spill` moves the top run into the vector when another entry has to go
on top. `unspill` brings the vector's last entry back into the state when
it is a run. Freeing a cell whose members defer one cell never touches the
vector.

*Fast paths and slow paths.*

```rust
pub unsafe extern "C" fn __reussir_drop_drain() {
    let state = state();
    if state.draining.get() { return; }
    if state.len.get() == 0 {
        match state.n.get() {
            0 => return,                          // nothing pending
            1 => return unsafe { drain_one() },   // one cell, no link was made
            _ => {}
        }
    }
    unsafe { drain_slow() }
}
```

`__reussir_drop_defer(_wide)` calls `try_defer` inline and falls back to
`defer_slow` only when the vector must grow. The slow paths (`defer_slow`,
`drain_slow`, `drain_one`) are `#[inline(never)]` `extern "C"` functions.
They cannot unwind, so the entry points reach them by tail calls, and the
fast paths need no stack frame. The table is emptied by a single store
(`known.set(0)`) instead of `Vec::clear`. `link`, `unlink`,
`release_index` and the drain loop keep 0014's logic and encoding.

**What stays the same.** The behaviour is 0014's: the entries, their order
(last pushed first, a record's last member first, host steps interleaved
as before), the links through cell headers, `depth()` and `active()` at
every event, and the public functions and their signatures. lean2rr's
runtime, which uses `active`, `depth`, `defer_step` and `run_step`, needs
no change.

**One edge difference.** The buffer of the stack is freed by a
thread-local guard registered when it is first allocated. Suppose a free
runs from a thread-local destructor that runs after that guard's, that is,
one registered before it. It then allocates a new buffer that is never
freed: at most 1.5 KB per thread exit. 0014 aborted in that situation
instead (a `RefCell` thread-local accessed after its destruction). lean2rr
cannot reach it: its thread-locals free nothing, and Lean code runs on one
thread.

**Verification.**

- New `reussir-rt` tests (`drop/tests.rs`). `random_drops_match_the_model`
  runs random forests of cells and steps: wide and narrow deferrals,
  immediates, inline releases, steps that push work, nested drains, and
  more release functions than the table holds. It compares them against a
  model with one stack entry per pending cell or step. `table_full` covers
  a full table. `digest` hashes every event together with the `depth()`
  and `active()` seen at it, so two implementations can be compared
  exactly. The hashes are identical to 0014's (400 random scenarios).
- The tests pass under Miri, with strict provenance, stacked borrows and
  tree borrows.
- Review round 5 compared old and new event by event on 31 million events
  (3000 random programs mixing deferrals, steps, nested drains, immediates
  and a full table). It also covered deep step chains, links at the ±2^39
  offset limits, ASan and LSan builds, the lean2rr runtime suite, and
  adversarial lean2rr programs (266 record types in one free, 300k-deep
  chains with handles and tasks). Everything was identical.
- `run.sh` has no separate line for this patch. The bug 13 lines are
  unchanged (FIXED) on the current build, which includes 0015.

**Result**, from the patch message (user cycles over lean2rr without
0014's code generation): deriv +17.5% → +8.7%, monadic-interp +20.2% →
+2.2%, cfold +5.3% → +1.3%; binarytrees and rbtree unchanged. In wall
time: about 90% of 0014's cost recovered on MonadicInterp and about half
on Deriv.

**Effect on lean2rr.** Speed only. Every lean2rr program frees records
through this stack, and its containers too, since leanrt uses the same
stack. The remaining cost of 0014 (a few percent on Deriv-like programs)
comes from deferring itself and from the calls in the generated glue.
Removing it would need a change to Reussir's code generator, which is not
planned. Release order and all other behaviour are exactly 0014's.

## Upstream note

- **0013.** The drop glue releases an rc member as "count == 1 →
  drop_in_place(member); free(member)". The free follows the recursive
  call, so releasing a list of N cells takes N stack frames (overflow
  above about 500k cells on an 8 MB stack). Inside drop glue no token can
  be reused, so the member can instead be released by a function that
  frees the cell first and releases the chain member last, as a tail call
  (a loop).
- **0014.** The drop glue frees one member per call. Even with the last
  member released by a tail call, a value deep along another member (a
  left-deep tree with fresh right children, a rose tree) recurses once per
  level and overflows the stack. Native Lean uses an explicit to-do list
  (`lean_del`). A per-thread stack of pending releases, drained by the
  outermost `drop_in_place`, with the links stored in the deferred cells'
  own headers (their count is known to be 1), fixes it at no memory cost
  per pending cell.
- **0015.** If 0014 were proposed upstream, this patch would be folded into
  it. The pending stack's per-cell entry points should avoid
  `RefCell<Vec>` thread-locals with destructors: one `Cell`-only,
  destructor-less thread-local state, the top run kept in it, and an early
  return for an empty or one-cell drain make the per-cell cost a few loads
  and stores.
