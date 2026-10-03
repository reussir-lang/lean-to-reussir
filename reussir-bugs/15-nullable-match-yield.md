# 15. A `match` on a `Nullable` whose arms yield a counted value does not compile

## Summary

**Kind:** bug. **Status:** does not affect lean2rr (it does not use
`Nullable`). No patch yet.

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
