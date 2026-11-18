# 30. The vector lowering pass merges the blocks of code without vectors (a compile-time cliff)

**Kind:** cost (build time). Not a bug: rrc's output is correct. rrc
runs MLIR's pass `convert-vector-to-llvm` on every module, also on one
without any vector. As a side effect that pass merges similar blocks in
every function. In one large function of lean2rr's tests the merged
blocks got up to 234,385 arguments, and the build took 16 to 18
minutes. Patch 30-a lowers the vector dialect without that merging. It
is an optimization of build time, and it has a cost: the code of
lean2rr's programs is 2.0% larger.

## Summary

**Kind:** cost. **Status:** patched (30-a), the last patch of the series
on upstream `36a55a0f` (Reussir branch `l2r-base13-r3-vec`, commit
`2e0bb232`; the patch file is its final form, `af801585`, which differs
only in a description string and in its test; 10 files, +210/-4).
`scripts/l2r.py` does not check for the patch: without it the programs
are the same, and one known program builds in minutes.

**Upstream (2026-11-18):** Open at `36a55a0f`: new with upstream's
vector work (#994). `l2r-base12` does not have the pass. The behaviour
is MLIR's (LLVM 23.1.2), and the pass has no option for it. Not
reported to Reussir (the maintainer takes changes from this directory)
and not reported to LLVM. A form of the patch for plain upstream exists
(Reussir branch `j2-vec2llvm-pristine`); the file in `patches/` is the
form that applies after 28-a.

## Context

- **The pass.** MLIR's `convert-vector-to-llvm` lowers the operations
  of the vector dialect. Upstream Reussir put it into the lowering
  pipeline (`crates/reussir-backend/src/pipeline.rs`, after the basic
  lowering; the pass is made in `lib/CAPI/Passes.cpp:259`). It runs at
  every optimization level, and no rrc option removes it.
- **The greedy driver** applies a pass's patterns. With its default
  configuration it also simplifies regions, and its level for that is
  the aggressive one: it merges blocks that have the same operations,
  and gives the merged block one argument for each operand that
  differs.
- This is the same root as [entry 28](28-sve-vector-storage.md): an
  MLIR pass for vectors that cleans up whole functions that have no
  vector. There the driver's answer was taken as a failure; here the
  cleanup itself is the cost.

## Symptom

lean2rr's runtime test `RtOutlineStates` (613 kB of `.rr`; its largest
function has 7619 lines) in the port's gates: 984 s and 1079 s from the
`.rr` to the executable, where the whole suite took 671 s on
`l2r-base12`. The test passes; only the build is slow.

Phases of that build, alone on the machine (wall seconds):

| Phase | `l2r-base12` | series before 30-a | the pass skipped (a measurement build) |
|---|---:|---:|---:|
| MLIR lowering pipeline | 2.9 | 490 | 2.6 |
| of it `convert-vector-to-llvm` | (no such pass) | 487 | 0 |
| LLVM optimization | about 0.8 | 432 | about 3.0 |
| LLVM code generation | about 2.8 | 0.7 | about 2.2 |
| total to the executable | 9.1 | 924 | 7.9 |

The module that the pass leaves is 47.6 MB (10.9 MB on `l2r-base12`);
44.5 MB of it are 54 lines, block headers and branches with up to
234,385 arguments. LLVM then needs 7 minutes for it. Six stack samples
inside the pass, 20 s apart, are all in `mlir::simplifyRegions` under
`applyPatternsGreedily`.

**A cliff, not a curve** (reduced variants of the test, the same
translator):

| Variant | Largest function, `.rr` lines | To the LLVM dialect, this base | `l2r-base12` | Largest count of block arguments |
|---|---:|---:|---:|---:|
| one of three segments | 2349 | 1.2 s | 1.3 s | 12 |
| two of three segments | 4857 | 2.4 s | 2.6 s | 131 |
| the full test | 7619 | 468 s | 5.3 s | 234,385 |

The merged blocks of the full test have 77, 377, 1877, 9377, 46,877 and
234,385 arguments: five times more at each level of merging.

## Cause

`convert-vector-to-llvm` applies its first sets of patterns with the
greedy driver's default configuration. So for each function, with or
without a vector, the driver merges similar blocks. When merged blocks
are merged again, the arguments multiply. The cost is exponential in
the depth of a chain of similar blocks, so a function a third smaller
is not affected.

Which blocks merge: arms of one shape in a large function. In lean2rr's
output these are, for example, the arms of a state machine that do the
same work on different values. No small input shows the multiplication:
six constructed shapes (five in plain MLIR, one in plain Reussir) all
merge to a linear number of arguments. What a small input does show is
the mechanism: MLIR's pass merges two arms without a vector into one
block with arguments.

## lean2rr

One program of the suite is on the wrong side of the cliff. The two
other large tests are not (`RtDepPolyRec`, `RtTArrKinds`: the pass takes
6.2 s and 3.9 s there). lean2rr has no way around it: no flag reaches
the pass, and cutting the function further only moves the cliff.

## Patch

[`patches/30-a-vector-to-llvm-patterns.patch`](patches/30-a-vector-to-llvm-patterns.patch),
`[conversion] lower the vector dialect without region simplification`.

- A new pass, `reussir-convert-vector-to-llvm`
  (`lib/Conversion/ConvertVectorToLLVM/`), does what MLIR 23.1.2's pass
  does with its default options, which are the options that upstream
  Reussir uses (it sets only the SVE switch): the same 15 sets of
  patterns in the same order, applied greedily with the result ignored
  as MLIR does, then the same conversion to the LLVM dialect.
- The one difference: region simplification is off in the first step.
  Folding and constant CSE stay on (the lowering patterns build on
  folds). MLIR's branches for Neon, x86 and two more extensions are
  left out: Reussir never turns them on.
- The C API's constructor, the JIT bridge and `reussir-opt` use the new
  pass.

**Tests.** `conversion/convert_vector_to_llvm.mlir`: two pairs of arms
without a vector stay separate blocks and no block has an argument
(with MLIR's pass both checks fail: two merged blocks with two
arguments each); a `vector.broadcast` is still lowered; the checks of
`vector_lowering.mlir` pass through the new pass. The test shows the
mechanism, not the multiplication.

## The trade-off

The merging that MLIR's pass did by accident also made lean2rr's code
smaller. Nobody had planned or measured that. 30-a takes it away:

- **Build time:** `RtOutlineStates` builds in seconds.
- **Run time:** no measurable effect (below).
- **Code size:** the executables of the 53 benchmark programs are 2.0%
  larger in `.text` (geometric mean); Cedar is 9.3% larger. Every
  program grows.

What the growth is made of (symbol sizes of the executables of timing
run 21, without and with 30-a):

| Program | `.text` symbols | Functions that grew | Where |
|---|---|---|---|
| L02 rbtree-ck | 863,624 to 880,076 (+16,452; 1.9%) | 2 of 2200 | one library function, `IO.Error.toString`: 10,620 to 27,448 bytes (+16,828), which is all of it |
| L18 hashmap | 1,010,540 to 1,028,264 (+17,724; 1.8%) | 11 of 2318 | `IO.Error.toString` +16,828: 95% |
| Z06 Cedar | 4,295,940 to 4,731,892 (+435,952; 10.1%) | 271 of 3488 (76 shrank) | spread: `Cedar.Spec.Value.extExprToValue` +79,568 (17% of the growth), `Std.Time.parseWith` +24,084, four instances of a message parser +13,508 to +23,248 each, `Cedar.Spec.call` +19,664, `IO.Error.toString` +16,828 (4%) |

So in a small program the growth is one cold library function, the same
16.8 kB each time: a match over the error constructors whose arms do
the same work on different fields. That statement holds for small
programs only. In a large program such as Cedar the growth is spread
over hundreds of functions, most of it in parsers and dispatchers of
the program itself. The functions that grow are functions with many
arms of one shape; ordinary functions do not grow.

Options that were looked at and not taken: keep MLIR's pass and live
with one build of 16 minutes; merge blocks on purpose with a bound (not
possible with MLIR's public interface without a copy of its block
merger, and any size threshold is a guess, because the cliff depends on
shape, not on size). A possible later step on lean2rr's side: the
dispatchers that lean2rr emits itself can share their equal arms. Not
done.

## Review

One round by an independent reviewer (local notes
`port13/reviews/RV4`, round 4): approved with one change, which is in
the patch (the commit message states the code-size effect; "many
similar arms" in the place of "many equal release sequences").

- *Faithfulness.* The reviewer compared the pass with MLIR's source at
  `llvmorg-23.1.2` item by item (pattern sets and order, options,
  conversion target, dependent dialects): the same, with one field of
  the driver's configuration changed. Nothing follows the patterns in
  MLIR's pass, so no step can be missing.
- *Run.* 23 plain-MLIR cases of vector code, each through MLIR's pass
  and the new one, without and with the SVE switch (46 pairs): **44 of
  46 lowerings are byte-identical.** The two that differ are one case
  with control flow: MLIR's pass merges its two arms into one block
  with an argument, the new pass keeps the two arms. The same
  operations, another block structure: the intended difference.
  Unreachable blocks are removed by both. An operation that neither
  pass can lower stays in both, and both pipelines then fail at the
  same place with a diagnostic.
- The 20 vector lit tests pass, among them three SIMD programs that run
  on the SVE machine.
- *The JIT bridge.* Its two changed lines are compiled and linked, not
  executed: nothing in the tree calls the bridge.
- Not installed on the build machine: clang-format, clang-tidy.

## Measured claim

**Build time** (the author's pair: the series before 30-a against the
same with the patch; the same driver command, one warm texture store on
a memory file system; `RtOutlineStates`):

| Phase | without | with 30-a |
|---|---:|---:|
| MLIR lowering pipeline (sum of the passes) | 536.2 s | 2.7 s |
| of it the vector pass | 531.9 s | 0.079 s |
| LLVM optimization | about 440 s | about 3 s |
| total to the executable | 977.7 s | 8.1 s (12.1 s in the first run) |
| widest block in the lowered module | 234,385 arguments | 2 arguments |

The executable's output is identical without the patch, with it and
natively. (The run without the patch shared the machine with other
work; alone it took 924 s.) In lean2rr's gate on the series with 30-a,
`RtOutlineStates` takes 10.7 s in rrc and the link, and the runtime
suite 652 s (671 s on `l2r-base12`).

The pass itself on two other large tests: `RtDepPolyRec` 6231 ms to
874 ms, `RtTArrKinds` 3907 ms to 478 ms. Their whole builds do not
change outside the noise of single runs.

**Run time** (timing run 21, 2026-11-18: the series without 30-a
against the series with it; direct pairs, median of 9 and min, the two
sides in turn; 53 cases): geometric mean 1.000 (0.9998). 52 of 53 cases
are inside ±3%. The one outside is X07 qsort, 0.933, faster with the
patch (a 20 ms case; not explained, so not a claim for the patch). The
slowest is 1.027. Cedar, where the code grows most: 1.021, 1.014,
1.000. Peak memory: no case outside 3%.

**Code size** (`.text` of the same 53 executables): geometric mean
1.020; sum 83,980,983 to 86,515,519 bytes. Cedar +9.3% (+463 kB, one
program in three cases), L04 +2.7%, L17 +2.4%; the smallest growth is
+0.5%. In a first measurement on 12 object files of lean2rr programs
the growth was 1.6% to 25% of the object's `.text` (the 25% is a 70 kB
object that gains the same 16.8 kB).

**Other code:** upstream's benchmark suite, core and std (33 units,
lowered MLIR): byte-identical with and without the patch. 72 output
files of upstream's vector tests and of tests without vectors: 70
byte-identical, 2 identical after the random names of Rust modules are
made equal.

**Not measured:** the exponential growth on a small input (not
reduced); lean-zip and Cedar build times with and without the patch; a
run of the JIT bridge.

**Repro.** [`repros/bug30-vector-lowering-merge.mlir`](repros/bug30-vector-lowering-merge.mlir) shows the mechanism through `reussir-opt`: MLIR's pass merges the arms of a function without a vector into blocks with arguments, and the pipeline's own pass leaves them (`run.sh` prints REPRODUCES or FIXED). It does not show the multiplication. Run on pristine `36a55a0f`: REPRODUCES; on the series of 15 patches: FIXED (2026-11-18, a run of the repro's author; the gate's own `run.sh` was from before the repro).

## Upstream note

Not reported. A report to Reussir would give the phase table and the
block-argument counts of the three variants. The MLIR behaviour (a
lowering pass for one dialect that simplifies the regions of all code)
is worth an LLVM report of its own, together with entry 28's.
