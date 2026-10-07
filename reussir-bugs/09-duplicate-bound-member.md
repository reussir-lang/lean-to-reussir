# 9. Duplicate bound members lose a reference in `RcDispatchFusion`

## Summary

**Kind:** bug. **Status:** patched (09-a, on `./reussir`'s `l2r-trim`;
since 2026-10-07 in the helper-only form of upstream pull request #653,
which does not need 07-a; it also fixes
[bug 14](14-member-consumed-before-release.md)).

**Upstream:** pull request #653 (open), with 09-a (which also fixes
entry 14).

When a match arm binds a constructor's fields, Reussir retains each bound
field and later releases the matched cell. `RcDispatchFusion` merges this
into one "destructuring" release: if the cell dies, each field's reference
simply moves to the arm. A cell holds exactly *one* reference per field,
though, and the pass did not check that it was replacing only one retain
per field, still unused at the release. Two shapes broke the count:

- bug 9 (this entry): a field retained twice (used twice). Both retains
  were erased.
- [bug 14](14-member-consumed-before-release.md): a field consumed before
  the release, for example stored in a new cell that is released again.
  The retain's reference was already gone.

Either way a field ends up with one reference too few, and is freed while
still in use (use after free). Patch 09-a fuses at most one retain per
field, and fuses nothing when a bound field is consumed before the
release.

## Symptom and repro

Repro [`repros/bug09-duplicate-bound-member.rr`](repros/bug09-duplicate-bound-member.rr)
(the core):

```
enum T { N(u64, T, T), L }
fn f(x : T) -> T {
    match x {
        T::N(a, l, r) => { let y : T = { let z : T = T::N { a, l, r }; x }; T::N { a, r, l } },
        T::L => x
    }
}
```

`go` runs `f` on 1000 fresh trees and prints how many checksums are wrong.
The shape usually appears after Reussir inlines a callee that drops the
scrutinee:

```
fn second(t : T, y : T) -> T { y }
fn f(x : T) -> T { match x { T::N(a, l, r) => second(x, T::N { a, l, l }), T::L => x } }
```

**Command.** `rrc bug09-duplicate-bound-member.rr` with lean2rr's flags.

**Expected.** `0`.

**Actual on ef922049.** SIGSEGV, at every `-O` level. (A single call of `f`
prints a wrong checksum in about half of the runs: `882` instead of `2432`
at `-O aggressive`, garbage at `-O none`; ASan reports a heap use after
free.) `run.sh` printed
`issue 09   REPRODUCES  use after free: SIGSEGV, expected 0`.

## Cause

`lib/Transformation/RcDispatchFusion/RcDispatchFusion.cpp`, `fuseArm`,
scans the arm's top level up to the scrutinee's release. It collects every
retain of a value loaded from the arm's payload, without checking for
duplicates:

```c++
if (auto inc = llvm::dyn_cast<ReussirRcIncOp>(op)) {
  if (extractedMemberIndex(inc.getRcPtr(), payloadRef)) {
    if (!inc.isSingleAcquire())
      return false;
    boundIncs.push_back(inc);          // no duplicate check
  }
  continue;
}
```

Then it erases them all and stamps the release with
`boundMembers = [index of each retain]`. It accepts any other op that has
no regions and does not touch the scrutinee, including ops that consume a
retained member (bug 14).

The expansion (`RcDecrementExpansion.cpp`) reads `boundMembers` as a *set*
on the unique path:

```c++
llvm::SmallDenseSet<int64_t> bound;
for (int64_t index : op.getBoundMembersAttr().asArrayRef())
  bound.insert(index);
... // release only members not in `bound`; the cell becomes a token
```

The unique path therefore transfers one reference per member, however
many retains were erased, so each duplicate loses a count and the member
is freed while still referenced. The shared path
(`rematerializeBoundRetains`) re-creates one retain per entry, which is
right.

**As the pass sees it.** `f`'s arm before fusion, dumped from
`rrc -t mlir -O none` plus the passes before `RcDispatchFusion` (types
shortened). `l` and `r` are used twice while `x` is still live:

```
%5 = reussir.ref.load (project %arg1 [1])      // l
%7 = reussir.ref.load (project %arg1 [2])      // r
reussir.rc.inc(%5)                              // for z
reussir.rc.inc(%7)
reussir.rc.inc(%5)                              // for the result
reussir.rc.inc(%7)
%11 = reussir.rc.create (T::N{%3, %5, %7})      // z
reussir.rc.dec(%11)                             // z is dead
reussir.rc.dec(%arg0)                           // x is dead (y unused)
%15 = reussir.rc.create (T::N{%3, %7, %5})      // the result
```

The unpatched pass erases all four retains and gives
`reussir.rc.dec(%arg0) {boundMembers = array<i64: 1, 2, 1, 2>, destructureTag = 0}`.
`x` is fresh, so its count is 1 and the unique path runs. `z` takes `l` and
`r` without owning a reference to either. Releasing `z` frees both. The
result is then built from freed cells.

The pure duplicate case is in the patch's test (`take_twice`):
`inc %tail; inc %tail; dec %l; call @pair(%tail, %tail)`. The unpatched
pass stamps `boundMembers = [1, 1]`. The unique path transfers one
reference where `pair` needs two.

## lean2rr

Lean's compiler removes the obvious forms (a dead construction, a value
used twice and then dropped), but Reussir's own inliner at `-O default`
and `-O aggressive` recreates them: a callee that drops its argument, like
`second` above, becomes a plain `rc.dec` after the retains. Review round 1
confirmed that `inl.rr` (the `second` shape) already prints a wrong
checksum at `-O default`. lean2rr cannot prevent that. The shapes are
silent memory corruption; they were not seen in the corpus or the test
suites, but they are reachable: a callee that drops its argument plus a
field used twice or stored in a dead value.

## Patch

Patch file
[`patches/09-a-fuse-retains-once.patch`](patches/09-a-fuse-retains-once.patch):
since 2026-10-07 the helper-only form, commit `670cfac6` of the
`./reussir` branch `pr/dispatch-fusion-member-retain` (upstream pull
request #653), as commit `fabae64b` of `l2r-trim` (its subject is the pull
request's). It adds `consumesFusedMember` itself, so it no longer needs
07-a, which is parked ([issue 7](07-phantom-reuse-donor.md)). The code of
`fuseArm` and the tests `take_twice` and `consume_then_take` are those of
the earlier form. That earlier form (`l2r-local` commit `e13c2e2c`, also
on `l2r-local` 136d9a9f) came after 07-a and called the helper that 07-a
added.

**The fix.** Two hunks in `fuseArm`. The first binds each member once and
erases only its first retain:

```c++
+  llvm::SmallDenseSet<int64_t> boundIndices;
   ...
-      if (extractedMemberIndex(inc.getRcPtr(), payloadRef)) {
+      if (auto index = extractedMemberIndex(inc.getRcPtr(), payloadRef)) {
         if (!inc.isSingleAcquire())
           return false;
-        boundIncs.push_back(inc);
+        // The box owns one reference per member, so only one retain per
+        // member can be replaced by the transferred owner; a further retain
+        // of the same member is a real copy and must stay.
+        if (boundIndices.insert(*index).second)
+          boundIncs.push_back(inc);
       }
```

The second fuses nothing when an op before the release consumes a bound
member (bug 14):

```c++
+  for (mlir::Operation &op : region.front()) {
+    if (&op == dec.getOperation())
+      break;
+    if (consumesFusedMember(op, boundIncs))
+      return false;
+  }
```

`consumesFusedMember(op, members)` (09-a adds it; before 2026-10-07, 07-a
added it) is true when `op` takes one
of the retained values as an operand and is neither `rc.borrow` nor
`rc.inc`.

**Why it is correct.**

- *One retain per member.* A unique cell contributes exactly one owned
  reference per field, so at most one retain can be replaced by it.
  Further retains of the same member are real copies and must stay.
  `fuseCompoundConsumption`, the compound version of this fusion in the
  same file, already did this ("Duplicate projections are additional real
  copies and keep their remaining retains").
- *No consumption before the release.* The erased retain's reference is
  replaced by the transferred one only at the release, so up to the release
  the retained value must not have been handed to anything. Every alias of
  a member is made by an op that takes the retained SSA value (a record
  construction, `nullable.create`, `ref.spilled`, a yield, a call), and all
  of them count as consuming. Releases of other values are harmless: each
  drops a reference its holder owns, and the scrutinee keeps every member
  alive until its own release. Review round 3 checked that no pass before
  dispatch fusion creates a second load of a member that could bypass the
  rule.
- Cases left unchanged: arms whose members are retained once and only
  borrowed before the release, which is the normal pattern-match shape,
  are fused exactly as before.

With the patch, the bug 9 repro is not fused at all, because `z` consumes
`l` and `r` before `x`'s release: it is fixed by the bug 14 rule. The bug
14 repro is not fused either. `take_twice` keeps one retain, with
`boundMembers = [1]`. The first version of 09-a, reviewed in round 2, had
only the duplicate rule. That already fixed the bug 9 repro: with one
retain per member kept, `z` owns its references. It did not fix bug 14
(round 2, finding R2-2), so the rule against consumption was added (the
revision after round 2). 07-a had the same flaw in its own scan, found in
the same review, and is fixed the same way.

**Verification.**

- Review round 1 found bug 9 in unpatched code (RV-3) with the generators
  (two failing seeds had duplicate `boundMembers` in their fused IR).
- Round 2 checked 09-a v1: the round-1 repros and seeds, a test with
  members used two and three times with an inlined dropper, duplicates
  inside a branch together with 07-a's sinking, and 611 programs from a
  generator with inlinable droppers, all correct and ASan-clean. It also
  found bug 14 in unpatched code (R2-2, also generator seed 5077).
- Round 3 checked the revised 09-a together with the revised 07-a: the
  targeted attacks listed under issue 7's verification and fuzzing with ASan
  (712 + 195 programs). It found no failure, and 25 programs that fail
  with unpatched rrc pass.
- FIXED (`0`) on the round-2 stack and with the revised 07-a/09-a. `run.sh`
  on the patched build:

      issue 09   FIXED       prints 0 (no wrong result in 1000 runs)   [lean2rr's flags]
      issue 14   FIXED       prints 0 (no wrong result in 1000 runs)   [lean2rr's flags]

  On the round-2 stack, with the first 09-a, bug 14 still crashed.

**Effect on lean2rr.** A member used twice, or consumed, before the
scrutinee's release keeps its count: the use-after-free shapes above are
gone. Some arms are no longer fused, namely those that store a bound field
in a new cell before releasing the scrutinee. No regression was measured
in the review rounds.

## Upstream note

`RcDispatchFusion`'s `fuseArm` erases every retain of a member loaded from
the arm's payload and lets the scrutinee's destructuring release transfer
the cell's references instead. But the cell owns one reference per
member, so (a) a member retained twice loses a count (`boundMembers =
[1, 1]`), and (b) a member consumed before the release (built into a cell
that is released first) loses the reference its retain provided. Both are
use-after-free, reachable after inlining a callee that drops the
scrutinee. Fix: bind each member once (as `fuseCompoundConsumption`
does), and do not fuse when a bound member has a non-borrow use before the
release.
