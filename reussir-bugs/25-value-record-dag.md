# 25. Copying a `[value]` record of shared sub-records expands exponentially

**Kind:** cost (build time; the expansion is deliberate). Not a bug: rrc's
output is correct, and there is no patch.

## Summary

**Kind:** cost (build time; the expansion is deliberate). **Status:** does
not affect lean2rr (its `[value]` records are shallow). No patch.

**Verdict: cost of a deliberate design, not a defect.** Copying or dropping
a `[value]` record retains or releases every counted value inside it.
Reussir's first acquire/drop expansion writes that work out in line, member
by member, through every nested `[value]` member. When records share
sub-records (`D(i) = { D(i-1), D(i-1) }`), the code is exponential in the
nesting depth: one copy of `D(K)` is 2^K retains. The in-line form is there
on purpose: it exposes each member's retain and release to the inc/dec
cancellation that runs next. Found by the review of the patch for
[bug 19](19-cell-of-value-record.md), which had the same shape in the
outlined acquire glue; that part is fixed by that patch (19-a).

## Symptom and repro

Repro [`repros/bug25-value-record-dag.py`](repros/bug25-value-record-dag.py)
`K OUT.rr` writes `S` (a shared box), `D0 = [value] { s: S, n: u64 }` and
`D(i) = [value] { a: D(i-1), b: D(i-1) }`; `main` builds one `D(K)` and uses
it twice, so it is copied once. The program prints `14`.

**Command.** `rrc OUT.rr --emit mlir-llvm -O default` (the LLVM-dialect
module, before LLVM).

**Expected.** A module and a build time about linear in K (the program is).

**Actual** (the same on 91da4f80 and on the final `l2r-local` cc8e5aa5):

| K | lines of the LLVM-dialect module | rrc |
|---|---|---|
| 6 | 1,935 | |
| 8 | 7,341 | 0.3 s |
| 10 | 28,875 | 1.0 s (91da4f80: 1.4 s, 342 MB) |
| 12 | 114,921 | 11.4 s, 208 MB |

About 2x per level. `run.sh` prints `issue 25   REPRODUCES  --emit
mlir-llvm: K = 8: 7341 lines, K = 10: 28875 lines (3.93x for two more
levels)`. The review measured the same shape without the FFI print
(`rv7/p22/x/u12.rr`, rv7/p22 round 1, on a build without 17-a) at 16 s and
4.7 GB; the final stack's 208 MB at K = 12 is probably patch 17-a
([issue 17](17-long-nat-block.md)), which removed the quadratic memory of the
SCF lowering: the code is as large as before.

## Cause

rrc's pipeline (`crates/reussir-backend/src/pipeline.rs`) runs
`AcquireDropExpansion` twice: the first phase (`(false, false)`, line 411)
before `ConvertToSTD` and the inc/dec cancellation, the second
(`(true, true)`, line 419) after them. The first phase expands each
`ref.acquire` and `ref.drop` of a `[value]` record in line:
`emitOwnershipAcquisition` (`lib/IR/ReussirOps.cpp`) and the drop patterns
(`lib/Conversion/AcquireDropExpansion/AcquireDropExpansion.cpp`,
`rewriteDropCompound`, `rewriteDropVariant`) project each member and recurse
into nested `[value]` members, down to the counted values. A record type
reachable along k paths is expanded k times, so `D(K)` costs 2^K. The
second phase outlines what is left into per-type glue functions that call
each other (linear).

The in-line first phase is deliberate: the expanded retains and releases of
the members are visible to `IncDecCancellation`, which cancels a retain
against a later release of the same value. It dates from upstream 4af21eb9
(#255, 2026-06-14), before the local patches.

The outlined acquire glue (`acquire_in_place`) had the same in-line
expansion in its body, so it was exponential too; the patch for
[bug 19](19-cell-of-value-record.md) (19-a, `callMemberGlue`) makes it call
the members' glue instead. The first phase is unchanged.

## lean2rr

Not affected. lean2rr's `[value]` records are shallow: field-less
enumerations, and `Nat` and `Int` (two arms of one word, or one word with
the one-word representation); every other record is a shared box, whose
copy is one retain. No workaround needed.

## Why it stays unpatched

A fix (a size threshold for the in-line expansion, or leaving nested named
records to the second phase) gives up some cancellation and would need its
own performance review. The review (rv7/p22, round 2) agreed: "older than
the patches, leave unpatched". lean2rr does not meet it.

## Upstream note

The first `AcquireDropExpansion` phase (pipeline.rs:411) expands a
`[value]` record's acquire/drop in line through every nested `[value]`
member, so records sharing sub-records in a DAG (`D(i) = { D(i-1), D(i-1)
}`) cost 2^K at each copy (K = 12: 115k lines of LLVM dialect for one
copy). A threshold, or leaving nested named records to the outlining
second phase, would bound it at some cost in cancellation.
