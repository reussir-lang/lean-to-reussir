# 19. A `Cell` of a `[value]` record with counted members does not compile

## Summary

**Kind:** bug. **Status:** worked around (lean2rr stores `Nat`/`Int`
references in two cells and boxes other `[value]` records). No patch yet.

`cell::get` and `cell::set` on a `Cell` of a `[value]` record with a counted
member pass a `field`-capability reference where the record's outlined
acquire or drop function expects one of unspecified capability, and rrc
rejects the call.

## Symptom and repro

Repro [`repros/bug19-cell-of-value-record.rr`](repros/bug19-cell-of-value-record.rr):

```
struct [shared] Bg(u64)
enum [value] Nat { Small(u64), Big(Bg) }
struct RNat(Cell<Nat>)
fn mk(v : Nat) -> RNat { RNat{core::intrinsic::cell::alloc(v)} }
fn run(n : u64) -> u64 {
    let r : RNat = mk(Nat::Small{n});
    let x : Nat = core::intrinsic::cell::get(r.0);
    match x { Nat::Small(y) => y, Nat::Big(b) => b.0 }
}
```

**Command.** `rrc bug19-cell-of-value-record.rr -O aggressive`.

**Expected.** Compiles; prints `42`.

**Actual on ef922049.**

    error: 'func.call' op operand type mismatch: expected operand type
    '!reussir.ref<!reussir.record<variant "_RC3Nat" [value] {...}>>', but provided
    '!reussir.ref<!reussir.record<variant "_RC3Nat" [value] {...}> field>' for operand number 0
    error: lowering pipeline failed: RunPass

`cell::set` fails the same way. With `Big(u64)` (no counted member) the
program compiles and prints `42`.

## Cause

`lib/Conversion/ConvertToSTD/ConvertToSTD.cpp` projects a cell's slot with
a `field`-capability reference (`getCellSlotRefType`) and emits
`ref.acquire` (get) or `ref.drop` (set) on it (`acquireThenLoadCellSlot`,
`dropThenStoreCellSlot`). For a named record type, `AcquireDropExpansion`
outlines these into the record's acquire and drop functions, whose
parameter is a `ref<T>` of unspecified capability
(`createDtorIfNotExists`, `emitOwnershipAcquisitionFuncIfNotExists`), and
calls them with the `field` reference unchanged. Cells of scalars, of
trivially copyable value records and of rc values take other paths and
work. `rrc -v` shows the failure in the second `AcquireDropExpansion` run
(the one that outlines record drops), after the first `ConvertToSTD` run
has materialized the Cell accesses.

## lean2rr

A reference to a `Nat` or `Int` (`ST.Ref`, `IO.Ref`) is the prelude's
`L2RNatRef`/`L2RIntRef`: a tagged word in a `Cell<u64>` and the big number
in a `Cell<L2RBigOpt>`. A reference to any other `[value]` record keeps the
element in an `ElemBox` (one allocation per `set`; such references do not
occur in practice, since lean2rr's `[value]` structs are IO results).
