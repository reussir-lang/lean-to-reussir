# 28. The uniqueness-carrying analysis proves a shared value unique

## Summary

**Kind:** bug (miscompile). **Status:** patched (0060).

**Verdict: bug.** At `-O aggressive`, Reussir's uniqueness-carrying
analysis can prove a value unique when it is fresh on one path but shared on
another. A self call on such a value then goes to a `.unique` clone of the
function, and the clone tells LLVM that the argument's count is 1. LLVM
takes the unique fast path, so the clone rebuilds the shared cell in place
and every other holder of that cell sees the change. The pass's own header
calls asserting uniqueness on a shared value "undefined behavior", and its
soundness test (`unique_carrying_soundness.mlir`) rejects the shared shapes
the pass recognizes. The bug is in its lattice: one value, `Unknown`, stood
both for "nothing known yet" and for "provenance unknown", and the join
treated it as the first.

## Symptom and repro

Repro [`repros/bug28-unique-carrying-join.rr`](repros/bug28-unique-carrying-join.rr):

```
struct B(u64)
struct P(B)
fn bump(b : B) -> B { B { b.0 + 100 } }                 // in place when b is unique
fn pick(a : B, p : P, n : u64) -> B { if n == 2 { p.0 } else { a } }
fn f(x : B, p : P, n : u64) -> B {
    if n == 0 { x } else { f(pick(bump(x), p, n), p, n - 1) }
}
#[main]
fn main() {
    let p = P { B { 1 } };
    let r = f(B { 5 }, p, three());                       // three() is an opaque 3
    say(r.0);
    say(p.0.0);
}
```

`f` returns its argument `x` on the base path, so it "carries" argument 0.
Its self call passes `pick(..)`: a fresh cell, or `p.0`, a field of `p`
that `p` still holds (count 2). At `n = 1`, `bump` rebuilds `p.0`'s cell.
That must produce a new cell, because the cell is shared.

**Command.** `rrc bug28-unique-carrying-join.rr -O aggressive`.

**Expected.** Prints `101` then `1`.

**Actual on ef922049.** Prints `101` then `101` at `-O aggressive`
(`101` then `1` at `-O none` and `-O default`, where the analysis does not
run). `run.sh` prints `bug 28   REPRODUCES  prints 101 101, expected 101 1`.
The same IR shape with an opaque call in place of the field
(`func.call @opaque` joined with an `rc.create`) also gets a `.unique` clone.

## Cause

The pass `reussir-unique-carrying-recursion-analysis`
(`lib/Transformation/UniqueCarryingRecursionAnalysis/UniqueCarryingRecursionAnalysis.cpp`)
runs first in the `-O aggressive` pipeline
(`crates/reussir-backend/src/pipeline.rs`, before the inliner). For each
rc value it computes a provenance (`UniqueCarryingValue`): `Unknown`, or a
pair `{fresh, carriedArgs}` meaning "on some path this value is a fresh
`rc.create` / the function's argument i". A function whose rc results are
all fresh or carried is "carrying"; a directly self-recursive carrying
function gets a clone `f.unique` that starts with `rc.assume_unique` on the
carried arguments, and every self call whose carried arguments are proven
unique is redirected to the clone. `rc.assume_unique` lowers to
`llvm.assume(count == 1)` (for types that cannot be tagged immediates;
`BasicOpsLowering.cpp`, `ReussirRcAssumeUniqueOpConversionPattern`).

The join was:

```c++
static UniqueCarryingValue join(const UniqueCarryingValue &lhs,
                                const UniqueCarryingValue &rhs) {
  if (lhs.unknown)
    return rhs;
  if (rhs.unknown)
    return lhs;
  ...union of the bits...
```

and the file header says why: "`Unknown` is absorbing in proofs (never
unique) and the identity of the join". But `Unknown` is also what the
evaluator returns for every value it cannot trace: a field loaded out of a
cell (`ref.load`), the result of a call to a function whose summary is
unknown, a block argument, a value disqualified by sharing. Joining such a
value with a fresh create gave "fresh", the value was proven unique, and
the self call went to the clone. A function declaration has no returns, so
its summary was `Unknown` as well, and a call to an external function also
dropped out of joins.

In the repro, `pick`'s result is the join of `p.0` (a load: `Unknown`) and
`a` (its argument 0), so `pick` is summarized as "argument 0"; at the call
site in `f` argument 0 is `bump(x)`, fresh, so `pick(bump(x), p, n)` is
"fresh" and `f`'s self call goes to `f.unique`. In the clone, `bump` is
inlined after the analysis, its release of `x` tests `count == 1`, and
LLVM folds the test to true from the assume: the cell of `p.0` is
overwritten with `101`.

## lean2rr

lean2rr builds with `-O aggressive`, so its output goes through this pass.
No lean2rr miscompile was seen: on three lean2rr programs (MapMIO, DepRet,
PickDep, under `~/Documents/l2r-scratch/examples/`) the clones made before
and after the patch are the same (4, 3 and 3: `List.reverseAux`,
`List.range.loop`, `l2r_mk_args`, `l2r_array_to_list`), so lean2rr also
loses no specialization. A Lean function that returns an argument on one
path and passes its self call a value that is fresh on one path and a
field (or an unknown call's result) on another would be miscompiled. For
enum types the assume is `tagged || count == 1`, and in the list variants
of the repro LLVM did not exploit it; structures, `Rc` scalars and arrays
get a plain `count == 1`. No workaround.

## Patch

Patch file
[`patches/0060-l2r-local-bug-28-make-Unknown-absorb-the-uniqueness-.patch`](patches/0060-l2r-local-bug-28-make-Unknown-absorb-the-uniqueness-.patch)
(made as commit `b8aedd37` in a scratch checkout on `91da4f80`, that is
the apply list + 0016 + 0017).

The two meanings are split. Bottom is the empty provenance set (no fresh
bit, no argument): the identity of the join, the start of a join over
arms, and the optimistic start of a function summary in the fixpoint.
`Unknown` is top and absorbs the join:

```c++
-  bool unknown = true;
+  bool unknown = false;
   ...
-  static UniqueCarryingValue getUnknown() { return {}; }
+  // No contributing path (yet): the identity of the join.
+  static UniqueCarryingValue getBottom() { return {}; }
+
+  // Unknown provenance: absorbing, never unique.
+  static UniqueCarryingValue getUnknown() {
+    UniqueCarryingValue value;
+    value.unknown = true;
+    return value;
+  }
   ...
-    if (lhs.unknown)
-      return rhs;
-    if (rhs.unknown)
-      return lhs;
+    if (lhs.unknown || rhs.unknown)
+      return getUnknown();
```

The places that used `Unknown` as a starting point now start from bottom:
`joinRegionYields` (the join over a dispatch's or an `if`'s arms), the
mapping of a callee's summary at a call site, and a function's summary.
Every `func.func` is seeded before the fixpoint: a function with a body at
bottom (as before: optimism about recursion), a declaration at `Unknown`
(its results may be anything). A callee missing from the summaries (not a
`func.func`) is `Unknown`.

**Why it is correct.** The lattice is now the usual one: bottom (no value
reaches here) below the provenance sets, ordered by inclusion, below top.
Every value the evaluator cannot trace is top, and top survives every join,
so a value is proven unique only if every path that can produce it is a
fresh create or an assumed argument. Bottom appears only where no path has
contributed yet (an empty join, a summary not computed yet, a callee that
never returns), where it contributes nothing. The fixpoint is unchanged in
kind: it starts at bottom for every defined function and applies a
monotone map (the call-site mapping sends top to top and bottom to bottom),
so it still terminates at the least fixpoint. For code without untraceable
contributors the results are the same as before: the existing tests
(`unique_carrying_recursion.mlir`, `array_unique_carrying_recursion*.mlir`)
pass unchanged.

**Verification.**

- New tests: `unique_carrying_soundness.mlir` gains an opaque-call-or-fresh
  self call (no clone, function not carrying) and a field-or-fresh result
  (not carrying); `frontend/unique_carrying_shared_field.rr` (the repro,
  with a C driver, at `-O aggressive` and `-O default`). Both fail on the
  unpatched build.
- Reussir's lit suite: 546 passed, 81 unsupported, none failed, with the
  four patches 0060 to 0063 (the unpatched build: 540 passed).
- lean2rr's runtime tests (14, among them RtFuzzReuse, RtShareMutators,
  RtFreshRebuildShared, RtReprShare, RtHashMap, RtPersistWalk): all pass.
- `run.sh`: `bug 28   FIXED       prints 101 1   [-O aggressive]`.

**Effect on lean2rr.** None measured: the same specializations on the
programs above; the informational attribute `reussir.carrying_uniqueness`
is on fewer operations (MapMIO: 179 before, 60 after), and nothing else
reads it.

## Upstream note

`UniqueCarryingRecursionAnalysis.cpp`: `UniqueCarryingValue::join` treats
`Unknown` as the identity, but `Unknown` is also the provenance of every
untraceable value (loads, unknown calls, declarations). A value that is
fresh on one path and, say, a field of a live cell on another is proven
unique, the self call goes to the `.unique` clone, and its
`llvm.assume(count == 1)` lets LLVM rebuild the shared cell in place
(repro: a self call on `if c { p.0 } else { fresh }` prints a mutated
`p.0` at `-O aggressive`). Fix: a separate bottom (empty set, identity,
fixpoint start) and an absorbing `Unknown`; declarations start at
`Unknown`.
