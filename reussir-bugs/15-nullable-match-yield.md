# 15. A `match` on a `Nullable` whose arms yield a counted value does not compile

## Summary

**Kind:** bug. **Status:** patched (0022), applied in `./reussir`
(`l2r-local` cc8e5aa5). It does not affect lean2rr (it does not use
`Nullable`).

**Verdict: bug.** `Nullable` matching is a surface feature with tests
(`crates/reussir-core/src/semi.rs`). Narrowed further (at `-O none`):
`NonNull(b) => x, Null => T::L{}` and `NonNull(b) => T::N{..}, Null => x`
fail; `T::L{}` in both arms or `x` in both arms compile, and so does a
shared struct in place of the enum.

## Symptom and repro

Repro [`repros/bug15-nullable-match-yield.rr`](repros/bug15-nullable-match-yield.rr):

```
struct [shared] B { v: u64 }
enum T { N(u64, T, T), L }
fn g(nb : Nullable<B>, x : T) -> T {
    match nb {
        Nullable::NonNull(b) => { x },
        Nullable::Null => { T::L{} }
    }
}
```

**Command.** `rrc bug15-nullable-match-yield.rr -O aggressive`.

**Expected.** Compiles; prints `1`.

**Actual on ef922049.**

    error: 'reussir.scf.yield' op parent operation expected a value, but nothing is yielded
    error: lowering pipeline failed: RunPass

`run.sh` printed `bug 15   REPRODUCES  rrc error: parent operation expected
a value, but nothing is yielded`; on the final stack it prints
`bug 15   FIXED       compiles, prints 1   [-O aggressive]`.

## Cause

Found while writing the local reports (2026-10-02, round 6); the entry
said "not investigated" before.

The match is lowered to `reussir.nullable.dispatch` in
`crates/reussir-codegen/src/lower/expr.rs` (`nullable_switch`). Its arms
end in `reussir.scf.yield` with the result, a `T`. The ownership analysis
releases `x` in the arm that does not use it (here the `Null` arm), as an
`rc.dec` of a counted enum. `RcDecrementExpansion` expands that release,
and the first run of `AcquireDropExpansion` expands the drop of its
contents in line as a `reussir.record.dispatch` on `T`'s tag, with no
result: its arms end in a bare `reussir.scf.yield`. That dispatch sits
inside the `Null` arm of the `nullable.dispatch`.

The verifier of `reussir.scf.yield` (`ReussirScfYieldOp::verify`,
`lib/IR/ReussirOps.cpp`) picks the op whose result a yield must produce by
looking for the nearest enclosing `nullable.dispatch` at any depth before
it looks for a `record.dispatch`:

```c++
  } else if (auto nullableParent =
          getOperation()->getParentOfType<ReussirNullableDispatchOp>())
    expectedType = nullableParent.getValue()
                       ? nullableParent.getValue().getType()
                       : mlir::Type{};
  else if (auto recordParent =
               getOperation()->getParentOfType<ReussirRecordDispatchOp>())
  ...
  if (expectedType && !yieldedType && !allowImplicitArrayResult)
    return emitOpError(
        "parent operation expected a value, but nothing is yielded");
```

So the inner dispatch's bare yields are checked against the outer
`nullable.dispatch`'s result type `T`, and rejected. Evidence:

- `rrc bug15-nullable-match-yield.rr -O aggressive -v` (with the
  polymorphic-FFI flags) prints `[mlir-pass] FAILED
  ReussirAcquireDropExpansionPass`, the first of its two runs (right after
  `ReussirInferVariantTagPass`).
- A hand-written module with a result-less `record.dispatch` (bare yields)
  inside the `null` arm of a `nullable.dispatch` that returns `i64` fails
  in `reussir-opt` alone with the same error; the same module whose
  `nullable.dispatch` has no result verifies.

This also explains the narrowing in the verdict: when no arm uses `x`
(`T::L{}` in both arms), the release of `x` is placed before the dispatch;
when both arms use `x`, no arm releases it; a shared struct's drop needs no
`record.dispatch`. Only a release of a counted enum inside an arm of a
`nullable.dispatch` with a result nests the two.

## lean2rr

Does not use `Nullable`.

## Patch

Patch file
[`patches/0022-l2r-local-bug-15-check-a-reussir.scf.yield-against-i.patch`](patches/0022-l2r-local-bug-15-check-a-reussir.scf.yield-against-i.patch)
(`l2r-local` commit `0f02c434`, applied in `./reussir`; `l2r-local` head
`cc8e5aa5`).

**The change.** `ReussirScfYieldOp::verify` (`lib/IR/ReussirOps.cpp`) now
checks every kind of parent the way it already checked
`array.create`, `cell.rdlock` and `array.with_unique_view`: against the
immediate parent op, the op whose single-block body the yield terminates.

```c++
+  mlir::Operation *parent = getOperation()->getParentOp();
   ...
   } else if (auto nullableParent =
-          getOperation()->getParentOfType<ReussirNullableDispatchOp>())
+                 llvm::dyn_cast_if_present<ReussirNullableDispatchOp>(parent))
   ...
   else if (auto recordParent =
-               getOperation()->getParentOfType<ReussirRecordDispatchOp>())
+               llvm::dyn_cast_if_present<ReussirRecordDispatchOp>(parent))
   ...
-  else if (auto arrayParent =
-               getOperation()
-                   ->getParentOfType<ReussirArrayWithUniqueViewOp>()) {
-    ...  // the nearest-ancestor fallback, now unreachable
-  } else
+  else
     llvm_unreachable("unexpected parent operation");
```

The bare yields of the variant drop's `record.dispatch` are now checked
against that dispatch (no result: nothing to yield), not against the
`nullable.dispatch` around it.

**Why it is correct.** The op's `ParentOneOf` trait already requires the
immediate parent to be one of the five ops, and MLIR verifies traits before
`verify()`, so the yield always belongs to its immediate parent and the
`llvm_unreachable` cannot be reached. The old nearest-ancestor lookup could
not have been meant for a yield inside a region that is not a dispatch: the
trait rejects those. The verifier accepts more IR (it no longer rejects a
correct nested dispatch); a nested yield of the wrong type is now caught by
this verifier too (`RegionBranchOpInterface` already rejected it before,
with another message). No generated code changes.

**Verification.**

- Tests: `tests/integration/basic/success/scf_yield.mlir` (nested
  dispatches with different results) and
  `tests/integration/frontend/nullable_match_counted_yield` (both arm
  orders, run end to end with a C driver).
- `run.sh` on the final stack: `bug 15   FIXED       compiles, prints 1`.
- On the final stack (all 34 patches): Reussir's lit suite, 645 tests, 564
  passed, 81 unsupported, none failed.

**Review.** Round 7, `p22` (`~/Documents/l2r-scratch/rv7/p22/FINDINGS.txt`):
no defect; the reviewer confirmed the trait argument above and that
"accepts only more IR" holds in effect (the two hand-written mismatched
modules under `v22/` are rejected by the patched and the unpatched rrc, with
different messages). Round 8 checked its interaction with 0020 (an
opaque-payload enum yielded from a `Nullable` match): correct at every
level.

**Effect on lean2rr.** None (no `Nullable`).

## Upstream note

`ReussirScfYieldOp::verify` (`ReussirOps.cpp`) finds a `nullable.dispatch`
parent with `getParentOfType`, the nearest one at any depth, before looking
for a `record.dispatch`, so the bare yields of a result-less
`record.dispatch` nested in a `nullable.dispatch` with a result are checked
against the outer op ("parent operation expected a value"). That is the
shape AcquireDropExpansion builds for a match on a `Nullable` whose arms
yield a counted value. Fix: check every parent kind against the immediate
parent, as `ParentOneOf` already requires.
