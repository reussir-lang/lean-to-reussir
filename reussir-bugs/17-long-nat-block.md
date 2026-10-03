# 17. rrc memory is quadratic in the length of a straight-line function on `Nat`

## Summary

**Kind:** cost (a stock MLIR pass's default mode), with a small local fix.
**Status:** patched (0031), applied in `./reussir` (`l2r-local`
5c0514e3); lean2rr also works around it (it cuts long functions into parts
and turns `Array Nat` literals into tables), and keeps doing so.

**Verdict (first: unclear; now found).** The quadratic memory is real and
also happens at `-O none` (N = 250: 418 MB at `-O aggressive`, 160 MB at
`-O none`; N = 500: 1.18 GB, 401 MB, including about 12 s of texture
build), so it is neither the inliner nor `--reuse-across-call`. The pass
was later found: MLIR's `convert-scf-to-cf`, run with the dialect
conversion driver's pattern rollback, which records every operation a
pattern moves (below). Upstream offers a mode without it for this pass;
0031 uses it.

## Symptom and repro

Repro [`repros/bug17-long-nat-block.py`](repros/bug17-long-nat-block.py)
`N OUT.lean [Nat|UInt64]` writes

```
def longDo (x0 : Nat) : Nat → Nat
  | 0 => x0
  | k+1 => Id.run do
    let x1 := (x0 * 3 + x0) % 1000003
    ...                     -- N lets
    return longDo xN k
```

built through lean2rr with its workaround turned off (`L2R_NO_OUTLINE=1`).
It prints the same number as native Lean.

**Command.** `L2R_NO_OUTLINE=1 scripts/l2r.py` on the generated module.

**Expected.** rrc memory about linear in N.

**Actual on ef922049** (rrc only, this machine):

| N | `Nat` |
|---|---|
| 250 | 21 s, 417 MB |
| 500 | 32 s, 1.16 GB |
| 1000 | 57 s, 4.1 GB |

The same block on `UInt64` (`bug17-long-nat-block.py 1000 OUT.lean
UInt64`): 20 s, 127 MB. Sizes that hit the limits (before lean2rr's
workaround): 2500 `let`s ran out of memory (`std::bad_alloc` at 14 GB); a
test with a 1500-`let` function needed 5.5 GB. `--reuse-across-call` is
not the cause (1000 `let`s took 4.1 GB without it too).

## Cause

The memory is taken in rrc's MLIR lowering pipeline: a build that stops
after it (`--emit mlir-llvm`) already reaches the peak (417 MB at N = 250,
1.19 GB at N = 500), while the IR it emits grows linearly (301k and 565k
lines). Every `Nat` operation was a match on a two-arm `[value]` enum
(lean2rr's `Nat` then; since patch 0050 it is one tagged word, and each
operation's inline fast path still branches on small or big), so
after ConvertToSTD the function is one block of N `scf.if` and
`scf.index_switch` operations. MLIR's `convert-scf-to-cf`
(`mlir::createSCFToControlFlowPass`, through `reussirCreateSCFToControlFlowPass`
in `lib/CAPI/Passes.cpp`) runs its patterns through the dialect conversion
driver, which by default records every operation a pattern moves so that
it can roll the conversion back. Lowering an `scf.if` (a switch, a loop)
moves the rest of its block into a new block, so a block of N of them
records about N²/2 moves: 16000 `scf.if` in one block take 8.4 s and
9.3 GB in `reussir-opt --convert-scf-to-cf`. (The first version of this
entry could not bisect by pass because the dump did not parse back,
[bug 29](29-ffi-member-mlir.md).)

## lean2rr

As for [bug 16](16-nested-io-matches.md), a function with a tail path (or a
`let` value) of 256 `let`s is cut into parts of at most 64 `let`s on a
path, recursive functions included (`LeanToReussir/Outline.lean`). rrc on
the 1000-`let` block: 877 MB (was 4.1 GB; the rest grows linearly, about
0.3 MB per `Nat` operation); the repro's recursive function with 1000
`let`s: 37 s and 0.9 GB for the whole build, with 2500: 66 s and 2.1 GB
(was out of memory). A spliced `Array Nat` literal, one push per element,
becomes a table (plan §5.12): a 100000-element literal is one call.
`run.sh` builds the repro with `L2R_NO_OUTLINE=1`.

## Patch

Patch file
[`patches/0031-l2r-local-bug-17-lower-SCF-to-ControlFlow-without-pa.patch`](patches/0031-l2r-local-bug-17-lower-SCF-to-ControlFlow-without-pa.patch)
(`l2r-local` commit `54cdf054`, applied in `./reussir`; `l2r-local` head
5c0514e3). The pass is created with `allowPatternRollback = false`, the
option upstream offers for it: the same patterns, applied without the
record.

```c++
 MlirPass reussirCreateSCFToControlFlowPass(void) {
-  return wrapOwned(mlir::createSCFToControlFlowPass());
+  mlir::SCFToControlFlowPassOptions options;
+  options.allowPatternRollback = false;
+  return wrapOwned(mlir::createSCFToControlFlowPass(options));
 }
```

**Why it is correct.** LLVM 23's contract for the mode
(`DialectConversion.h`, the pass's documentation): a pattern must not fail
after modifying the IR and must not produce IR that cannot be legalized;
if either happens, the driver raises a fatal error or fails the pass, and
never silently produces wrong code. The SCF lowering patterns (for, if,
index_switch, while, execute_region, parallel, forall) all return failure
before they modify anything. The 16000-`scf.if` block: 1.0 s and 142 MB,
identical output.

**Verification.** On the repro through lean2rr (`L2R_NO_OUTLINE=1`, rrc
time and peak memory): 250 lets 19 s, 427 MB -> 19 s, 318 MB; 500: 30 s,
1.17 GB -> 27 s, 610 MB; 1000: 57 s, 4.1 GB -> 53 s, 0.95 GB; 2000 (did
not build before): 134 s, 1.7 GB. The LLVM IR rrc emits is identical (up
to the random names of texture modules) for the 18 programs of lean2rr's
classic corpus and four lean2rr repros; the lit suite passes.

`run.sh` measures three sizes. Its first version compared rrc's memory at
N = 500 and N = 250 and called a ratio of at most 1.6x linear; with 0031
it printed 1.70x and 1.94x (`OTHER`). The measure was wrong, not the fix:
about 140 MB of rrc's memory does not depend on N (the prelude, the
runtime glue, the FFI textures), a third of the total at N = 250, so a
linear cost gives a ratio of 1.7-1.9x. `run.sh` now also builds N = 10 and
compares the memory each further `let` costs from 10 to 250 and from 250
to 500: about 1x when linear. Two runs each:

    final stack:  bug 17   FIXED       rrc: N = 10: 140 MB; N = 250: 31 s, 337 MB; N = 500: 47 s, 556 MB (each let: 0.82 MB up to 250, 0.88 MB from 250 to 500, 1.07x)
                  (second run: 141, 335, 578 MB, 1.19x)
    without 0031: bug 17   REPRODUCES  rrc: N = 10: 141 MB; N = 250: 31 s, 435 MB; N = 500: 55 s, 1151 MB (each let: 1.22 MB up to 250, 2.86 MB from 250 to 500, 2.34x)
                  (second run: 142, 427, 1145 MB, 2.41x)

(`without 0031`: 91da4f80, the apply list + 0016 + 0017.) The thresholds
are now FIXED at most 1.5x, REPRODUCES at least 1.9x.

**Review.** Round RV8C (`~/Documents/l2r-scratch/rv8/reussir-c/FINDINGS.txt`,
Q2): no defect. The reviewer checked the mode's contract in LLVM 23, that
every SCF lowering pattern fails before modifying IR, and ran
`reussir-opt --convert-scf-to-cf` with and without rollback over every lit
input containing SCF ops (66 files): identical output and diagnostics.

**Effect on lean2rr.** Build time and memory without lean2rr's outlining
(1000 `let`s: 4.1 GB -> 0.95 GB); lean2rr keeps its outlining and its
`Array Nat` tables.

## Upstream note

`convert-scf-to-cf` with the default pattern rollback records every
operation a pattern moves; lowering an `scf.if` moves the rest of its
block, so a block of N `scf.if` costs O(N²) time and memory (16000:
9.3 GB). `SCFToControlFlowPassOptions::allowPatternRollback = false`
(offered upstream for this pass) removes it with identical output.

