# Patch 0007: token reuse picks decrements that can never free (bug 7)

> **Audit (2026-10-02):** an optimization, not a bug fix. The output is correct without it; `fuseArm` stops at branches by design and TokenReuse's choice of donor is a heuristic. It stays because 0009 uses `consumesFusedMember`, which this patch adds; see bug 7 in `docs/reussir-bugs.md`.

Patch file: `../0007-l2r-local-bug-7-sink-bound-retains-into-the-branch-t.patch`
(`l2r-local` commit `fd860cbf`). Bug section:
[docs/reussir-bugs.md, bug 7](../../docs/reussir-bugs.md#7-token-reuse-picks-decrements-that-can-never-free).

## 1. Summary

A binary-search-tree insert that returns the matched node unchanged for an
equal key, `t` instead of `Node{l, x, r}`, ran about 6x slower than the
version that rebuilds the node. On the paths that do rebuild, the node's
cell should be reused for the new node. Instead Reussir allocated a new
node at every level and freed the old one. Because `t` stays alive on the
equal-key path, Reussir retains `t`'s children before the branch. On the
rebuilding paths, releasing `t` releases those children again. Those
releases can never free anything, yet token reuse offers them as donor
cells and prefers them to `t`'s own cell. The patch moves the children's
retains into the branch. The paths that release `t` then get Reussir's
efficient "destructuring" release: the children move to the arm, and `t`'s
cell becomes the reuse token. The paths that keep `t` get a retain and
release side by side, which a later pass cancels.

## 2. Symptom

Repro `docs/reussir-bugs/bug07-phantom-reuse-donor.rr` (the main part):

```
enum Tr { Leaf, Node(Tr, u64, Tr) }
fn ins(t : Tr, k : u64) -> Tr {
    match t {
        Tr::Leaf => { Tr::Node{Tr::Leaf{}, k, Tr::Leaf{}} },
        Tr::Node(l, x, r) => {
            if k < x { Tr::Node{ins(l, k), x, r} }
            else { if x < k { Tr::Node{l, x, ins(r, k)} } else { t } }
        }
    }
}
fn ins_b(t : Tr, k : u64) -> Tr {      // the same, but the equal arm rebuilds
    ... else { Tr::Node{l, x, r} } ...
}
```

`main` builds a 100,003-key tree with each, then inserts 3,000,000 keys
that are all present, and prints both sizes and the time ratio
`t(ins) / t(ins_b)`.

Command: `rrc bug07-phantom-reuse-donor.rr` with lean2rr's flags (`-O
aggressive --no-pack-record-members --reuse-across-call`).

- Expected: `100003 100003 ratio ...` with the ratio near 1: both inserts
  reuse the cells on the path.
- Actual on ef922049: a ratio of 6.12 (5.8-7.9 over runs); `ins` allocates
  a new node at every level of every insertion. `run.sh` printed
  `bug 07   REPRODUCES  insert returning t is 6.65x the rebuilding insert`.

## 3. Root cause

**Background: dispatch fusion.** The frontend lowers
`match v { C(a, b) => ... }` into a borrowing dispatch whose arm loads each
bound member, retains it (`rc.inc`), and later releases the scrutinee
(`rc.dec v`). The release drops the cell's own references to the members
again. `RcDispatchFusion`
(`lib/Transformation/RcDispatchFusion/RcDispatchFusion.cpp`, `fuseArm`)
turns "retain the members, release the cell" into one *destructuring
decrement*. It erases the retains and tags the `rc.dec` with the arm's tag
and the bound member indices. `RcDecrementExpansion` expands that into:

- if the count is 1, release only the *unbound* members and keep the cell
  as a reuse token; the bound members' references move to the arm;
- otherwise, retain the bound members and decrement.

This is Koka's `dropn_reuse`. It is what lets a rebuild reuse the
scrutinee's cell cheaply.

**Why `ins` misses it.** `fuseArm` scans the arm's top level for the
release of the scrutinee and gives up at the first op with regions:

```c++
// Region-bearing or opaque ops before the release: bail (the release
// may be conditional or the box may escape).
if (op.getNumRegions() > 0 || llvm::isa<mlir::CallOpInterface>(op))
  return false;
```

`ins`'s `Node` arm, as `RcDispatchFusion` sees it. This was dumped with
`rrc -t mlir -O none` and the passes before it; types are shortened:

```
[1] -> { ^bb0(%arg2: !reussir.ref<Tr::Node>):
  %3 = reussir.ref.load (reussir.ref.project %arg2 [0])     // l
  %5 = reussir.ref.load (reussir.ref.project %arg2 [1])     // x
  %7 = reussir.ref.load (reussir.ref.project %arg2 [2])     // r
  reussir.rc.inc(%3)                // retain l and r: t may stay alive
  reussir.rc.inc(%7)
  %9 = scf.if (k < x) {
    reussir.rc.dec(%arg0)           // release t (plain, transitive)
    %10 = func.call @ins(%3, k)
    ... rc.create Node{%10, %5, %7} ...
  } else {
    %11 = scf.if (x < k) {
      reussir.rc.dec(%arg0)         // release t
      ... rc.create Node{%3, %5, ins(%7, k)} ...
    } else {
      reussir.rc.dec(%3)            // t is kept: release the
      reussir.rc.dec(%7)            // extra references to l and r
      scf.yield %arg0
    }
  }
}
```

The unpatched pass leaves this arm unchanged (it fuses only the `Leaf`
arm), because `scf.if` comes before any `rc.dec %arg0`.

**What token reuse then does.** On the rebuilding paths, `rc.dec %arg0` is
a plain release. If `t`'s count is 1, its expansion drops `t`'s contents,
which releases `l` and `r` again. Those member releases are themselves
expanded as "count == 1 → drop and keep the token". But `l` and `r` were
retained above, so their counts are at least 2 there, and they never free.
They still produce (always null) tokens of the exact size of a `Node`. The
same happens on the equal-key path with `rc.dec(%3)` and `rc.dec(%7)`,
while `t` still holds the children. TokenReuse's `heuristic` gives every
exact-size token the same score. On a tie, `oneShotTokenReuse` prefers the
token whose producer comes later in its pre-order walk (`tokenOrderKey`),
"prefer the most recent producer". So the construction is given a token
from a member release that is null at run time, and allocates, while `t`'s
real cell is freed. docs/reussir-bugs.md adds that a decrement of a
nullary constructor (an immediate) is the same kind of phantom donor.

## 4. The fix

When `fuseArm`'s scan reaches an op with regions, it now calls
`sinkBoundRetainsIntoBranch` instead of giving up.

```c++
-    if (op.getNumRegions() > 0 || llvm::isa<mlir::CallOpInterface>(op))
-      return false;
+    if (op.getNumRegions() > 0 || llvm::isa<mlir::CallOpInterface>(op))
+      return sinkBoundRetainsIntoBranch(&op, boundIncs, tag, scrutinee,
+                                        payloadRef);
```

**`isSingleShotBranch(op)`** accepts an op that runs exactly one of its
regions exactly once: `scf.if` *with* an else, `scf.index_switch`,
`reussir.record.dispatch`, `reussir.nullable.dispatch`, each region a
single block. Loops are excluded. An else-less `scf.if` is excluded too,
because its empty path would lose the retain.

**`sinkBoundRetainsIntoBranch(branch, boundIncs, ...)`** moves the arm's
member retains from before the branch into the start of every region,
under these conditions:

- The branch is single-shot, and the retains are in its block.
- Between the first retain and the branch there are only retains,
  `ref.acquire`, borrows, projections, loads, `record.coerce`,
  `record.tag` and other region-free ops without memory effects. So
  nothing in that window releases any value, calls a function or has
  regions. A release there could drop the last owner of the scrutinee:
  when the scrutinee is a member borrowed from an enclosing match, its
  parent's release can free it.
- Each member is retained only once (no duplicate indices), and the
  retained values have no use before the branch other than borrows.
- Somewhere inside, the branch releases the scrutinee or one of the bound
  members. Otherwise the move gains nothing.

Each region then gets clones of the retains, and **`fuseSunkRetains`**
continues the scan there, mirroring `fuseArm`. The first release of the
scrutinee becomes a destructuring decrement over the sunk members, and the
clones are erased. A nested single-shot branch receives the retains in
turn. Anything else stops the scan and leaves the retains at the region's
start, which is equivalent to their old position.

**`consumesFusedMember`** (added in the revision after review round 2): no
fusion inside a region if an op before the scrutinee's release uses a
bound member other than by a borrow or a retain. Such a use (building the
member into a cell that is then released, for example) gives away the
reference the retain provided. The release's transferred reference would
then replace a reference that no longer exists (see 0009.md, bug 14).

The same `ins` arm after the patched pass (dumped with a build that has
the final 0007):

```
  %9 = scf.if (k < x) {
    reussir.rc.dec(%arg0) {boundMembers = array<i64: 0, 2>, destructureTag = 1}
    ... ins(%3, k) ... rc.create Node{%10, %5, %7} ...
  } else {
    %11 = scf.if (x < k) {
      reussir.rc.dec(%arg0) {boundMembers = array<i64: 0, 2>, destructureTag = 1}
      ...
    } else {
      reussir.rc.inc(%3)            // sunk retains meet the member releases:
      reussir.rc.inc(%7)            // reussir-inc-dec-cancellation removes
      reussir.rc.dec(%3)            // all four
      reussir.rc.dec(%7)
      scf.yield %arg0
    }
  }
```

Both rebuilding paths now hand `t`'s cell over as a token, with `l` and
`r` moved rather than retained. On the equal-key path, the retain/release
pairs cancel, so no phantom donors remain.

**Why it is correct** (from the patch's comments and message):

- Nothing between a retain's old and new positions can free a cell or
  observe a count (the window rule). So whatever held a member at the
  retain's old position (the scrutinee, or the enclosing cell a borrowed
  scrutinee belongs to) still holds it at the new one.
- The branch runs exactly one region, once, so every path still performs
  each retain exactly once, before its region's first operation.
- Inside a region, fusing into the scrutinee's release is the same
  transformation `fuseArm` already did at the top level, under the same
  conditions plus the consume rule.

**What it leaves alone.** The scan still stops at a call before the
branch. In lean2rr output a `Nat` or `String` key comparison is a call
(`lean_nat_dec_lt`), so 0007 rarely fires there; review round 1 noted this.
Else-less ifs and loops are left alone.

## 5. Verification

- Review round 1 passed 0007. It covered the window whitelist (every pure
  Reussir op was checked to neither release nor free), nested matches,
  re-matching the scrutinee, deep if/switch nests, inc/dec-cancellation
  interplay, differential fuzzing (gen to gen4, 5615 programs, no failure
  specific to the patch), and lean2rr BST/red-black/AVL/TreeMap programs
  against native Lean.
- Round 2 found a use after free (R2-1): `fuseSunkRetains` fused even when
  a sunk member was built into a cell released before the scrutinee's
  release, with the scrutinee shared. A generator built for this shape hit
  it in 5 of 248 programs. The revision added `consumesFusedMember`.
- Round 3 reviewed the revision ("I could not break the author's
  argument"). It ran targeted attacks (the scrutinee also passed as a
  second argument and released first, a member passed separately, a
  borrowed inner scrutinee whose parent is released, containers built from
  members in both orders) and fuzzed 712 + 195 programs with ASan. It
  found no failure.
- Measured (docs/reussir-bugs.md): the BST above allocates exactly like
  the rebuilding version (0.74 s → 0.16 s). A TreeMap-shaped insert
  without lean2rr's workaround drops from 12.35 to 1.33 allocations per
  insertion. The repro's ratio is 0.86-1.36 on the round-2 stack and
  0.95-1.13 with the revision.
- `run.sh` on the current build (a timing ratio, on a loaded machine):
  `bug 07   FIXED       insert returning t is 1.04x the rebuilding insert`.

## 6. Effect on lean2rr

lean2rr keeps its own workaround (plan §5.5, the optional passes
`nullary-scrutinee`, `lazy-fields` and `sink-proj`). In an arm where the
matched value stays live because it is stored or returned whole, lean2rr
binds only the fields used while the value is live, and matches again
where it dies. No phantom retains are produced, even on unpatched
Reussir. That workaround covers the `Nat`/`String`-keyed case that 0007
does not reach (a call before the branch). 0007 covers shapes the passes
do not rewrite, such as `UInt64` keys.

Not fixed (docs/reussir-bugs.md): about 0.33 extra allocations per
insertion remain from decrements of values that may be nullary immediates.
They still count as exact-size donors and can win the tie-break. Ranking
the matched cell above them fixed it in a trial (rbtree 1.48 → 0.98 s),
but cost monadic-interp 1.7%, so it was left out.

## 7. Upstream note

When a match's scrutinee stays alive on some path, its arm retains the
bound members before a branch, and `fuseArm` gives up at that branch. The
paths that release the scrutinee then release the members through the
transitive glue with counts ≥ 2. Those decrements never free, but
TokenReuse scores their tokens like the scrutinee's own cell and prefers
them (most recent producer), so the rebuild allocates and the real cell is
freed: a BST insert that returns `t` for an equal key is about 6x slower.
Suggested fix: sink the bound retains into a single-shot branch that
releases the scrutinee, and fuse there.
