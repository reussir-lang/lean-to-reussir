# 19. A `Cell` of a `[value]` record with counted members does not compile

## Summary

**Kind:** bug. **Status:** patched (0023, with 0033's composition fix),
applied in `./reussir` (`l2r-local` cc8e5aa5); lean2rr also works around it
(it stores `Nat`/`Int` references in two cells and boxes other `[value]`
records).

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
program compiles and prints `42`. `run.sh` printed `bug 19   REPRODUCES
rrc error: operand type mismatch`; on the final stack it prints
`bug 19   FIXED       compiles, prints 42   [-O aggressive]`.

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
lean2rr keeps this representation with 0023 applied (README policy:
workarounds stay, so that lean2rr also works with an unpatched Reussir).

## Patch

Patch file
[`patches/0023-l2r-local-bug-19-give-a-cell-s-value-record-its-own-.patch`](patches/0023-l2r-local-bug-19-give-a-cell-s-value-record-its-own-.patch)
(`l2r-local` commit `c9e640b3`, applied in `./reussir`; `l2r-local` head
`cc8e5aa5`), as amended after review round 7 (RV7P-01). Its composition
with 0033 ([bug 11](11-sccp-call-graph.md)'s symbol table collection) is
fixed in 0033 (RV8C-01, below).

**The change.** The capability of the argument reference becomes part of
the outlined glue, as the atomic kind already is:

- `createDtorIfNotExists` and `emitOwnershipAcquisitionFuncIfNotExists`
  (`lib/IR/ReussirOps.cpp`, declared in `include/Reussir/IR/ReussirOps.h`)
  take a `Capability cap`, and a `field` reference gets its own symbols:
  `drop_in_place_field`, `acquire_in_place_field`, and the `_atomic_field`
  pair (`RecordType::getDtorName`/`getAcquireName`,
  `lib/IR/ReussirTypes.cpp`).
- `AcquireDropExpansion` outlines `unspecified` and `field` references
  (`hasOutlinedGlue`) and passes the reference's capability; any other
  capability (`rigid`, `flex`) is expanded inline, as before:

  ```c++
  +bool hasOutlinedGlue(RefType refType) {
  +  return refType.getCapability() == Capability::unspecified ||
  +         refType.getCapability() == Capability::field;
  +}
  ...
  -            mlir::func::FuncOp dtor = createDtorIfNotExists(
  -                moduleOp, recordType, rewriter, refType.getAtomicKind());
  +            mlir::func::FuncOp dtor =
  +                createDtorIfNotExists(moduleOp, recordType, rewriter,
  +                                      refType.getAtomicKind(), refCap);
  ```

- `emitOwnershipAcquisition` projected a compound's members, and typed a
  variant's arm references, as `unspecified` references; for a `field`
  parent that failed (`ref.project` requires the parent's capability, and
  the dispatch lowering coerces with the scrutinee's). Both now take the
  parent reference's capability, as the drop expansion does.
- The amendment (RV7P-01): with a new `callMemberGlue` argument, set when
  an outlined acquire function is built, a compound member that is a named
  record is acquired by a call to its own acquire function (for the
  member's capability) instead of being expanded inline. The acquire glue
  then calls each other, like the drop glue, and its size is linear in the
  nesting depth even for records shared in a DAG
  (`D(i) = {D(i-1), D(i-1)}`).

**Why it is correct.** For references of unspecified capability, the only
kind that reached these paths in programs that compiled before, the inline
expansion is unchanged; the outlined acquire glue of a record with named
record members now calls their glue instead of inlining it, which acquires
the same members. A `field` glue is drop glue like the others
(`kDropGlueAttr`), so its non-leaf shared boxes go through the pending
stack and are drained at its end. Outlining a `rigid`, `flex` or `field`
reference failed `func.call` verification before, so no program that
compiled took the new symbols.

**The composition fix (0033, RV8C-01).** 0033 gives the acquire/drop
expansion one `SymbolTableCollection` per run, kept up to date by the two
glue creators. With 0023, the acquire glue of a record also creates its
named members' glue while its body is built (`callMemberGlue`), through a
call that did not get the collection: the member's glue was added to the
module but not to the collection, and a later lookup of that glue in the
same pass missed it and defined it again ("redefinition of symbol named
'_RINvNvC4core9intrinsic22acquire_in_place_fieldC4PairE'"), depending on
the order of the accesses. The final 0033 passes the collection on through
`emitOwnershipAcquisition` to that creation.

**Verification.**

- Tests: `tests/integration/frontend/cell_value_record` (with a C driver:
  get and set of a variant, of a compound and of a nested compound, a cell
  freed holding a counted arm, at `-O default` and `-O aggressive`; the
  field glue of the nested record calls the inner record's field glue) and,
  from 0033, `cell_value_record_glue_order` (a `Cell<Pair>` read before a
  `Cell<Quad>`, the order that failed). The first fails without 0023, the
  second on a stack with the first version of 0033.
- The MLIR and LLVM IR of Reussir's frontend tests (except the new tests)
  and the LLVM IR of 30 lean2rr programs are the same before and after.
- Compile cost of the review's DAG repro (get/set/get of a `Cell<D(K)>`):
  at K = 10, `rrc --emit mlir-llvm -O default` 4.6 s and 2.4 GB against
  11.7 s and 4.6 GB with the inline expansion of the first version. The rest
  is the first, inline, acquire/drop expansion phase, which is exponential
  for such records with or without a cell: pre-existing, documented
  separately as [bug 25](25-value-record-dag.md).
- `run.sh` on the final stack: `bug 19   FIXED       compiles, prints 42`.
- On the final stack (all 34 patches): Reussir's lit suite, 645 tests, 564
  passed, 81 unsupported, none failed.

**Review.** Round 7, `p22` (`~/Documents/l2r-scratch/rv7/p22/FINDINGS.txt`),
round 1: no miscompile and no regression; only references whose capability
is not unspecified take the new paths (every frontend and pass creator of
`ref.acquire`/`ref.drop` uses unspecified references, except cell slots);
differential fuzzing (68 seeds, 272 builds: cells and `RefCell`s of
`[value]` records with get, set and read-modify-write, aliased handles,
closures) gave identical normalized IR wherever both rrcs compiled and
correct outputs with as many frees as allocations. One finding, RV7P-01
(low): a `field` reference was never outlined, so every cell access
expanded the record inline, exponentially in a DAG of records (t10: 14.5 s
and 4.6 GB; t12: 273 s and 73 GB). Round 2 (`round2/FINDINGS.txt`): the
amendment fixes it (glue per capability, each function created once with
the right name, linear glue); a second fuzz (65 seeds, 260 builds, deeper
types and mutually recursive records through cells) and the "IR unchanged"
claim (147 frontend tests, 10 lean2rr programs) held. Round 8, `reussir-c`
(`~/Documents/l2r-scratch/rv8/reussir-c/FINDINGS.txt`): RV8C-01 (medium)
in the composition with 0033, fixed in the final 0033 as above; with that
fix the full lit suite passes on the composed stack.

**Effect on lean2rr.** None today (it keeps its two-cell references).
`Cell`s of `[value]` records with counted members compile, so lean2rr could
store a `Nat` or `Int` reference in one cell.

## Upstream note

`cell::get`/`cell::set` and a cell's drop glue reach the slot through a
`field` reference, and AcquireDropExpansion outlines `ref.acquire`/
`ref.drop` of a named record into glue whose parameter is an unspecified
reference: "'func.call' op operand type mismatch". Fix: glue per
capability (`unspecified` and `field` symbols), project members and arms
with the parent's capability, and let outlined acquire glue call the
members' glue (otherwise its size is exponential in a DAG of records).
