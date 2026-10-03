# Patch 0013: releasing a long list recurses once per cell (bug 13)

> **Audit (2026-10-02):** a missing feature implemented locally, not a bug fix: Reussir's drop glue recurses by design and Reussir never promises bounded-depth frees; Lean's semantics need them. See bug 13 in `docs/reussir-bugs.md`.

Patch file: `../0013-l2r-local-bug-13-release-chains-of-cells-in-a-loop-in-the-drop-glue.patch`
(`l2r-local` commit `2f4d25e1`). Bug section:
[docs/reussir-bugs.md, bug 13](../../docs/reussir-bugs.md#13-drop-glue-recurses-once-per-cell-of-a-long-list).
Patches 0014 and 0015 build on this one (0014.md, 0015.md).

## 1. Summary

When the last reference to a list goes away, Reussir's generated "drop
glue" releases the list's cells. For each cell it releases the members,
recursing into the tail, and only afterwards frees the cell. Because the
free comes after the recursive call, the call is not a tail call: freeing
a list of N cells needs N stack frames. Around 500,000 cells overflow an
8 MB stack; lean2rr's 1 GiB main thread overflows at about 33 million.
Native Lean frees iteratively. With 0013, a release inside the drop glue
calls a new per-type function, `drop_and_free`. It frees the cell first,
then releases the member that continues the chain as its very last action,
a tail call that LLVM turns into a loop. 0014 later replaced 0013's choice
of chain members with a stack of pending releases; the loop part
remains.

## 2. Symptom

The program needs no recursion of its own (docs/reussir-bugs.md):

```lean
def main (args : List String) : IO Unit := do
  let l := List.replicate 40000000 7
  IO.println s!"{l.head?}"
```

Repro `docs/reussir-bugs/bug13-long-list-drop.rr SHAPE N`, plain Reussir
with `main` on the 8 MB main thread:

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

SHAPE 0 is Lean's `List` (recursive member last). SHAPE 1 is a snoc list
(recursive member first, a box last). SHAPE 2 is a left spine (the chain in
the first of two `T` members). There is also a Lean repro,
`bug13-long-list-drop.lean CASE N`: `List.replicate N 7`, or a snoc list
`SnocS.snoc : SnocS → String → SnocS`.

Commands: `rrc bug13-long-list-drop.rr` with lean2rr's flags, then
`./bug13 0 1000000`; `scripts/l2r.py` on the Lean file, then
`./prog 0 40000000`.

- Expected: the plain repro prints N; the Lean repro prints `(some 7)` or
  `0`, like native Lean.
- Actual on ef922049:
  - Plain, 8 MB stack: `thread 'main' has overflowed its stack` (SIGABRT).
    A list takes 16 bytes of stack per cell and overflows above about
    524,000 cells; the snoc list and the left spine take 32 bytes per cell
    and overflow above about 261,000.
  - lean2rr, 1 GiB stack: `Stack overflow detected. Aborting.` (exit 134).
    33,437,500 cells work, 33,906,250 abort.
  - At 10 million elements (lean2rr, best of 5, max RSS):

    | | `List.replicate` | snoc list |
    |---|---|---|
    | native Lean | 0.08 s, 313 MiB | 0.08 s, 313 MiB |
    | ef922049 | 0.18 s, 617 MiB | 0.17 s, 541 MiB |
    | 0013, first version | 0.08 s, 312 MiB | 0.16 s, 541 MiB |
    | 0013, extended (the patch file) | 0.06 s, 312 MiB | 0.07 s, 236 MiB |

    The extra 300 MiB on ef922049 is stack: 10 million frames of 32 bytes
    stay resident.
- `run.sh` printed, for each shape,
  `bug 13   REPRODUCES  list, 1M cells, 8 MB stack: overflowed its stack (SIGABRT)`
  (and `snoc`, `lspine`), and for the Lean repro
  `bug 13   REPRODUCES  lean2rr List.replicate, 40M cells, 1 GiB stack: Stack overflow (SIGABRT)`
  (and `snoc`).

## 3. Root cause

**Drop glue.** For a named record type `T`, `createDtorIfNotExists`
(`lib/IR/ReussirOps.cpp`) creates `drop_in_place::<T>(ref<T>)`. It drops
the *contents* of a cell (its body is a single `ref.drop`); the caller
frees the cell. `AcquireDropExpansion`
(`lib/Conversion/AcquireDropExpansion/AcquireDropExpansion.cpp`) expands
`ref.drop`: a variant becomes a dispatch on the tag, and a compound becomes
one drop per managed member. An `rc` member becomes, in `rewriteDropRc`,
"load the member; `rc.dec` it". That `rc.dec` produces a token, like any
release. In its second phase (expand decrements, outline record drops) the
pass expands that `rc.dec` through the same pattern as
`RcDecrementExpansion`: "count == 1 → drop the member's contents (a call to
`drop_in_place` of the member's type) and take the member's cell as a
token; else count − 1". No construction can use a token inside drop glue,
so TokenReuse frees it, in the unique branch after the call.

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

## 4. The fix

The patch file holds the *extended* version, which review round 3
checked. Its hunks:

**Mark the glue** (`ReussirOps.h`, `ReussirOps.cpp`). The new attribute
`kDropGlueAttr = "reussir.drop_glue"` is set on every `drop_in_place`, and
later on every `drop_and_free`. Inside these functions no token can be
reused.

**Release differently inside the glue** (`rewriteDropRc`). If the enclosing
function has `kDropGlueAttr` and the member type `releasesThroughDropAndFree`,
the member is loaded and `emitGlueRelease` emits:

```
if (count == 1) call drop_and_free::<T>(member)   // likely
else            rc.set(member, count - 1)
```

`releasesThroughDropAndFree` holds for plain shared boxes (non-atomic,
non-regional) of a named, complete record that has at least one chain
member in some arm.

**`drop_and_free::<T>(cell)`** (`getOrCreateDropAndFree`, named
`_RINvNvC4core9intrinsic13drop_and_free<T>E`, `linkonce_odr`, private). It is
only called on a cell whose count was read as 1. Its body dispatches on the
arm and, per arm (`emitCellRelease`):

1. returns at once for a nullary arm of a taggable type under the
   special-pointer-tag scheme: an immediate, a static dummy whose count may
   have wrapped to 1 (bug 6), so nothing to free;
2. loads the chain members;
3. drops every other managed member (`ref.drop`, the ordinary glue);
4. frees the cell with its arm's size (`getVariantArmAllocSize` for a
   fused variant header);
5. releases the chain members (`emitChainRelease`).

**Chain members** (`chainMembers`) are the plain shared record boxes of the
arm whose type can hold the cell's type again (`reaches`: the cell's
recursive group, through records, boxes and nullable links), wherever they
sit. If there is none, it is the arm's last managed member, if that is
such a box. So `L::Cons`'s chain is its tail, `Snoc::S`'s is its first
member, `T::N`'s is both children, and a mutually recursive pair follows
each other.

**`emitChainRelease(links)`.** With one link, it is `emitGlueRelease`, the
final operation of the function: a tail call. With several, it first reads
all the counts and decrements the links whose count is not 1. Of the links
whose count is 1, it releases all but the last one that is unique first,
then the last one as the final operation:

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
chains still overflow there. Of a cell's chain members being freed, only
the last is a loop. The others are released by ordinary (recursive) calls,
so a tree deep along a child that is not the last still recurses. 0014
handles that case. Chains through `Nullable` links or closures, and atomic
(`Arc`) spines, still recurse (review round 4, finding R4-5).

**History.** The first version, reviewed in round 2, released only the
cell's *last managed member* by tail call. It fixed `List` and the right
spine, but the snoc list and the left spine still overflowed (round 2,
finding R2-6). The extension above, which chooses the members of the
recursive group wherever they sit, is what the patch file contains.

## 5. Verification

- Review round 2 (first version): 40M-cell chains on an 8 MB stack (list,
  a list whose `[value]` head holds a box, mutual recursion, a right spine)
  were fine at `-O aggressive` and `default`, ASan was clean at 1M cells,
  and the Lean `LongDrop` cases passed. It also measured binarytrees +3.4%
  on one core type (R2-5).
- Round 3 (extended version): all chain shapes, including the left spine
  and `Snoc(Snoc, Box)`, at 40M cells. ASan with leak detection was clean on
  DAGs (each child held twice), two long chains in one tree, chains through
  value records, a mutual group through a struct, and a chain whose middle
  cell is kept alive elsewhere. Forced-wrap tests of bug 6 passed, and the
  Lean `LongDrop` cases matched native. Binarytrees was within noise (+2%
  on one core type) and Deriv 5% faster (R3-1).
- `run.sh` on the patched build: all three plain shapes print
  `bug 13   FIXED       list, 1M cells, 8 MB stack: prints 1000000` (and
  `snoc`, `lspine`). Per docs/reussir-bugs.md, both Lean cases are FIXED at
  40M cells from the extended version on.

## 6. Effect on lean2rr

lean2rr cannot avoid releasing long lists or other chains of records, since
every Lean program that builds one drops it eventually. With 0013, freeing
them is a loop, at native speed and memory or better (table above). With
the first version, `List.replicate 40000000` already took 0.25 s against
native's 0.37 s, with native memory. What 0013
alone still misses (values deep along two members at once) is the subject
of 0014. lean2rr's runtime now requires 0014, which replaces part of this
patch's code.

## 7. Upstream note

The drop glue releases an rc member as "count == 1 → drop_in_place(member);
free(member)". The free follows the recursive call, so releasing a list of
N cells takes N stack frames (overflow above about 500k cells on an 8 MB
stack). Inside drop glue no token can be reused, so the member can instead
be released by a function that frees the cell first and releases the
chain member last, as a tail call (a loop).
