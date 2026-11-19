# 32. A record with an integer member loses the fast paths of the drop glue

**Kind:** cost (run time). Not a bug: the program is correct and the
order of releases is right. Upstream's drop glue has three fast paths
for recursive records. It turns all of them off for a record that
"reports an observable cleanup", and a record with a `Nat` or `Int`
member reports one, although the release of an integer runs no program
code. lean2rr's trees with integer keys and its expression types lose
the fast paths. Patch 32-a lets the glue ask the members. It is an
optimization.

## Summary

**Kind:** cost. **Status:** patched (32-a), patch 11 of the series on
upstream `36a55a0f` (Reussir branch `l2r-base13-r7`, tree `6dc99546`; 246 added and 53 removed lines; `WorklistDrop.cpp` +103/-53,
the rest tests). `scripts/l2r.py` does not check for the patch: without
it the programs are the same and frees of such records are slower.

**Upstream (2026-11-18):** Open at `36a55a0f`: new with upstream's drop
series of 2026-11-01. The local patches of `l2r-base12` (23-h, 23-i
and 23-j of the deleted entry 23,
[history](README.md#history-entries-19-23-and-24-deleted-2026-11-18))
had these fast paths for such records. Not reported: the maintainer takes changes from
this directory. The patch applies to a clean `36a55a0f` alone, and in
either order with 31-a.

## Context

- **Worklist drops.** A recursive record that is no list is freed
  through the runtime's work list: a dead child is *deferred* (put on
  the list) and popped later. A free that starts in user code *enters a
  scope* (`__reussir_drop_run`).
- **Three fast paths of upstream's glue**
  (`lib/Conversion/AcquireDropExpansion/WorklistDrop.cpp`):
  - *leaf dispatch* (`dispatchLeaf`): a dead value whose arm reaches no
    other box is released where it is found, with no scope;
  - *pure release* (`releasePure`): a cell's dead children are
    decremented, and the glue continues in the last dead one with a
    tail call, with no deferral for it;
  - *inline finish* (`canFinishInline`): a member whose whole cleanup
    can finish at once is released at the visit.
- **The flag.** `computeRecordDrop` (`lib/IR/RecordDrop.cpp:112-116`)
  marks a record as having an observable cleanup when it has a member
  that is not a record, nullable, box, array or cell, and is not
  trivially copyable. That is a default for every such type, not a
  decision about integers: no upstream test asserts it for an integer,
  and upstream's own tail-loop drop releases an integer member in
  place (the test `rcgmp_members.mlir` expects it).

## Symptom

Timing run 20 (the port against dev on `l2r-base12`): programs that
free large structures were slower. The two that were looked at, with
the same `.rr` on both sides:

```
enum T_Tree { c_Leaf, c_Node(T_Tree, Nat, T_Tree, T_color, bool) }
enum Expr   { c_val(Int), c_var(LStr), c_add(Expr, Expr), c_mul(Expr, Expr), c_pow(Expr, Expr), c_ln(Expr) }
```

Allocations and frees are identical on both bases. What differs is how
often the runtime is entered (counted with breakpoints):

| Runtime entry | deriv, `l2r-base12` | deriv, series before 32-a | rbtree-ck, `l2r-base12` | rbtree-ck, series before 32-a |
|---|---:|---:|---:|---:|
| scopes entered | 2 | 565,495 | 40,016 | 40,016 |
| children deferred | 928,916 | 2,426,392 | 204,963 | 1,053,560 |

deriv enters a scope for each dead `val(Int)` leaf that user code
releases, and both programs defer every freed node.

## Cause

All three fast paths ask the record's flag. `Tree` has a `Nat` key and
`Expr` has an `Int` arm (and a string arm), so both are "observable":

- `dispatchLeaf` refuses the record, so a dead leaf released from user
  code calls the type's entry, which opens a scope;
- `releasePure` is off, so every dead child is deferred and popped
  again, with no tail call;
- `canFinishInline` is off for the record (these two programs do not
  reach it).

But the release of an integer calls rcgmp's free, which ends in the
allocator. No hook and no program code runs, so nothing can observe
when it happens inside one free.

## lean2rr

Every lean2rr type with a `Nat` or `Int` field next to recursive fields
is affected: trees with integer keys, expression trees with integer
leaves. In timing run 20, twelve of 53 cases were slower than on
`l2r-base12`; seven of them are this entry's (below).

## Patch

[`patches/32-a-integer-members-pure-release.patch`](patches/32-a-integer-members-pure-release.patch),
`[drop] release integer members in place and tail-release the last
child`.

The glue asks the members, with one classification (`classify`):

- **`Leaf`**: scalars and integers only;
- **`Boxes`**: also shared boxes whose release can wait (not a foreign
  object, not a closure);
- **`Ordered`**: anything else.

Then:

- An arm that is a `Leaf` is released where it is found, its integers
  in place, with no scope (the leaf dispatch, under both drop orders).
- **Under backward drop order**, `releasePure` serves every arm that is
  not `Ordered`: it decrements the boxes, releases the integers in
  place, defers the dead boxes but the last, and continues in the last
  dead one with a tail call. An `Ordered` arm keeps the ordered
  release.
- **Under forward drop order** the pure release stays as upstream has
  it (records with no observable cleanup only). Only the leaf dispatch
  is new there.

**Why the order of hooks does not change (backward).** The ordered walk
also decrements every box at its visit and defers the dead ones, and
the drain pops the last deferred first. The pure release does the same
decrements in the same order, defers the same boxes, and calls the last
dead one directly: the one that the drain would pop next, with the same
work below it.

**Why forward order is left out.** The forward walk decrements a box
only when its turn comes. With a box that a child's subtree and a later
member share, a release that decrements everything first lets the
shared box die inside the earlier child's cleanup, before that child's
own hooks. The first version of this change (the prototype) used the
new rule under both orders. lean2rr uses backward order only, so it
never ran that; the review did (below).

**Tests.** `conversion/worklist_integer_members.mlir` (a leaf arm of an
integer released in place with no scope; an arm with a foreign object
keeps the ordered release; an arm of two boxes and an integer has the
in-place release, one deferral and the tail calls; under forward order
only the leaf arm changes). It fails on pristine upstream.
`conversion/worklist_pure_order.mlir` with a C driver (hooks behind the
boxes of a pure record run in the walk's order under both drop orders,
with a shared box; a chain of 100,000 needs no stack). This one passes
on pristine too: it guards the order.

## Review

Accepted by an independent reviewer (local notes `port13/reviews/RV2`,
the section on 32-a). The reviewer could not break it.

- **Order.** 3,080 generated scenarios with 151,906 hook events (a
  recursive type with 19 kinds of arms and a second, mutually recursive
  type; values that die whole, with an outer holder, as members of
  value records, as elements of arrays and of foreign vectors), at two
  optimization levels: under backward order the sequence of hooks is
  the same without and with the patch in every scenario; under forward
  order too.
- **The forward exclusion is needed.** The prototype, which used the
  pure release under forward order as well, changes the hook order in 9
  of 1,400 scenarios; 32-a changes none.
- **Memory.** 11 spines of 10^6 nodes dropped on a 256 kB stack: no
  stack overflow, no growth of peak memory in the drop, one scope each.
- **Integers.** 900 scenarios for each configuration, about 7,400
  integer allocations: none left alive, none freed twice; also next to
  a tagged handle (10-a).
- Findings, open as follow-ups, none blocking:
  - *G1.* No lit test pins the forward exclusion (the order test passes
    on pristine and would pass if the pure release were enabled under
    forward order). A test-only follow-up is described, not written.
  - *G2.* The code grows (below); the commit message now says so.
  - *G3.* A dead box whose payload is a structure of integers (a pair
    of `Nat`s behind a box, as a child) is still deferred. A small
    follow-up would release it in place. What it would gain on real
    programs is not measured; none of the timed programs has the shape.
  - *G4.* With three or more boxes, the tail call takes only the last
    dead one; a dead first box is still deferred. A cost only.

## Measured claim

**Wall time** (timing run 21, 2026-11-18: the series with 31-a and 32-a
against the series before them; direct pairs, median of 9 and min, the
two sides in turn; 53 cases; the `.rr` byte-identical on both sides).
Eight cases are outside ±3%, all faster. One is 31-a's (X10). The other
seven are 32-a's:

| Case | before | with | ratio (median) | (min) |
|---|---:|---:|---:|---:|
| X02 deriv | 61.6 ms | 51.8 ms | 0.829 | 0.838 |
| L03 deriv | 3799.2 ms | 3195.9 ms | 0.841 | 0.839 |
| L02 rbtree-ck | 715.2 ms | 607.5 ms | 0.849 | 0.855 |
| X06 rbtree_ck | 21.4 ms | 18.7 ms | 0.855 | 0.876 |
| E06 expr_eval | 55.6 ms | 51.6 ms | 0.875 | 0.927 |
| X03 cfold | 35.6 ms | 34.0 ms | 0.946 | 0.955 |
| L05 cfold | 566.1 ms | 544.2 ms | 0.961 | 0.960 |

Over the 53 cases the two patches together: geometric mean 0.975 (by
set 0.980, 0.989, 0.941, 0.996). No case is slower (the slowest ratio
is 1.023, inside the band). Peak memory: no case outside 3%.

**32-a alone** (timing run 22, 2026-11-18: the series of 12 patches
with 32-a against the same without it; direct pairs, median of 9 and
min; 20 cases: the seven above, X10 and 12 controls with the largest
change of their objects): X02 0.831, L03 0.837, L02 0.850, X06 0.857,
E06 0.875, X03 0.946, L05 0.963; the 13 others 0.993 to 1.007; no case
slower; X10 does not move with it (1.000). So the two patches' effects
are separate. The other 33 cases were not timed with 32-a alone.

**Counts** (the prototype, the same code): scopes entered on deriv
565,495 to 1; children deferred on deriv 2,426,392 to 652,241, on
rbtree-ck 1,053,560 to 204,963 (the count of `l2r-base12`). Call sites
of `__reussir_drop_run` in the optimized IR: X02 94 to 31, L03 97 to
34, X03 15 to 6. The reviewer's spines of 10^6 nodes: 999,999 deferrals
to 0 for a tree with an integer key; 2,999,999 to 1,999,999 with a hook
behind a box at each node.

**Cost, code size.** Optimized IR lines without and with 31-a and 32-a:
X02 +3.8%, Z01c +0.3%, L12 +0.2%. `.text` of the 53 executables:
geometric mean 1.001. The object of one unit of upstream's benchmark
suite +4.4%. The worst case seen is a synthetic type with 19 arms: its
object's text +39% at the aggressive level.

**Other code:** upstream's benchmark suite, core and std (33 units,
lowered MLIR): 3 change (bigint-rbtree, nbe-hoas and std gain tail
calls in their release helpers and lose deferrals), 30 are
byte-identical. Upstream's programs with such records were compiled,
not run.

**Through lean2rr:** 16 release-order and memory tests pass on the
series with 31-a and 32-a, and `alloc-check.sh` on the four deep-free
tests passes with peak memory at or below native's; the gate on the
series with all 15 patches passes (748 of 750, 2 expected failures),
and so does the gate on the series of 16.

**Not measured:** the follow-up G3; forward order through lean2rr (lean2rr does not use it).

## What is left against l2r-base12

Derived for each case as this run's ratio times run 20's ratio (two
sessions, not a direct pair): the 53 cases are at 0.959 of dev on
`l2r-base12`. Four cases are still above 1.03: L18 hashmap 1.077, X07
qsort 1.075, L08 unionfind 1.062, L15 monadic-interp 1.054. They did
not move with 31-a and 32-a (1.002, 1.002, 1.000, 1.003). Timing run
23 looked at them in direct pairs: X07 was code placement and is at
1.001 with the series of 16; L08's cause is found and patched
([entry 34](34-leaf-integer-foreign-release.md): 1.010 with 34-a);
L15 (1.044 on the series of 17) and L18 (1.055) are investigated and
not fixed. For each, about half of the difference is the cost of
destruction-scope entries (about 4.2 ns for each entry), and the other
half is not located. Each remaining part is under 3%, so they are not
pursued
([history](README.md#history-the-move-to-36a55a0f-2026-11-17), steps
9 and 10).

The formatter (clang-format 23.1.0, LLVM style, 2026-11-19) moved line
breaks in 27 of 32-a's changed lines and changed no token.

**Repro.** [`repros/bug32-integer-member-release.mlir`](repros/bug32-integer-member-release.mlir) shows the static difference through `reussir-opt`: the release of a variant with integer members has no tail release (REPRODUCES) or has one (FIXED). In the gate on the series of 16 patches (2026-11-18): REPRODUCES on pristine `36a55a0f`, FIXED on the series.

## Upstream note

Not reported. A report would give the two types, the counts of scopes
and deferrals, and the seven pairs. The change keeps upstream's rule
for forward order and its order of hooks for backward order.
