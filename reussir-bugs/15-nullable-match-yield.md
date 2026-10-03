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

Not investigated (the match is lowered to `reussir.nullable.dispatch` in
`crates/reussir-codegen/src/lower/expr.rs`, `nullable_switch`; the error
comes from the pass pipeline).

## lean2rr

Does not use `Nullable`.
