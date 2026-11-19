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
on upstream `36a55a0f` (Reussir branch `l2r-base13-r7`, tree `6dc99546`; 10 files, +210/-4). A form of the patch that applies to
plain upstream is in
[`patches/standalone/`](patches/standalone/).
`scripts/l2r.py` does not check for the patch: without it the programs
are the same, and one known program builds in minutes.

**Upstream (2026-11-19):** Open at `36a55a0f` and on upstream's main
(`c2861a55`): new with upstream's vector work (#994). `l2r-base12`
does not have the pass. The behaviour is MLIR's (LLVM 23.1.2), and the
pass has no option for it. Pull request reussir#1100 is open. Its
first form was the series' 30-a (region simplification `Disabled`).
The maintainer asked for a justification of turning the whole step
off, and the form now in review sets the level `Normal`: only the
block merging is off
([the levels](#region-simplification-and-its-levels)). **The series
keeps `Disabled` for now; it is to be switched to the form that
upstream accepts when reussir#1100 resolves.** Not reported to LLVM. The file in `patches/` is the form that
applies after 28-a; the form for plain upstream is
`patches/standalone/30-a-vector-to-llvm-patterns.patch`.

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

## Region simplification and its levels

Read from MLIR 23.1.2's greedy driver. After the driver applies its
patterns, it can simplify the regions of the code. The step has three
levels:

| Level | What the driver does after the patterns |
|---|---|
| `Disabled` | nothing |
| `Normal` | removes unreachable blocks; removes dead operations and dead block arguments |
| `Aggressive` | the same, and merges identical blocks and drops redundant block arguments |

Block merging makes one block of blocks that have the same successors
and the same operations; each operand position that differs becomes a
new block argument. There is no finer switch than the three levels.

- **MLIR's vector pass has block merging only through the driver's
  default.** The pass calls the greedy driver with no configuration,
  and the driver's default level is `Aggressive`. MLIR's own
  canonicalizer pass has `Normal` as its default.
- **Reussir's own code never asks for `Aggressive`.** Where it sets a
  level at all, it turns region simplification off (its inliner, its
  JIT bridge, and the storage pass of patch 28-a). The canonicalizer
  passes of rrc's pipeline, before and after the vector pass, run at
  `Normal`: none merges blocks. So nothing depends on the merging for
  correctness; it changes code size only.
- **The vector patterns do not need the cleanup.** The patterns that
  were read create no block and no branch (one creates a structured
  `scf.if`). Measured: `Normal` and `Disabled` give byte-identical
  output on every input that was tried (85 files of upstream; objects
  of 6 lean2rr programs).

**The two forms of the patch.** The series' 30-a sets `Disabled`. The
form in upstream's review (reussir#1100) sets `Normal`. They differ
only in the cleanup of unreachable blocks and dead operations, which
finds nothing after these patterns. `RtOutlineStates` to the
executable: 924 s with MLIR's pass (one run), 8.67 s with `Disabled`,
8.83 s with `Normal` (medians of 3); the executable's output is the
same in all three.

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
smaller. Nobody had planned or measured that. 30-a takes it away. The
whole trade, as measured:

- **One program builds:** `RtOutlineStates` goes from about 16 minutes
  to 11 s.
- **Small programs are about 9% slower to build:** +0.15 s of rrc and
  the link for each small test (1.68 s to 1.83 s), slower in 20 of 20
  tests. The cost is 30-a's alone (below).
- **Large programs are not slower to build:** lean-zip 37.6 s without
  the patch, 35.0 s and 36.9 s with it; Cedar 78.2 s and 83.3 s
  without, 76.4 s and 77.6 s with.
- **Code size:** the executables of the 53 benchmark programs are 2.0%
  larger in `.text` (geometric mean); Cedar is 9.3% larger. Every
  program grows.
- **Run time:** unchanged (1.000 over 53 cases).

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
- The patch's changed lines are clean under clang-format 23.1.0 (LLVM
  style) since 2026-11-19; the formatter moved line breaks in 6 lines
  and changed no token. clang-tidy was not run.

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
are inside ±3%. The one outside is X07 qsort, 0.933. It is not a gain of the
patch: the hot function is the same machine code on both sides, and
the patch moved its start address by 16 bytes (timing run 23; the
times of four builds follow that address). The
slowest is 1.027. Cedar, where the code grows most: 1.021, 1.014,
1.000. Peak memory: no case outside 3%.

**Code size** (`.text` of the same 53 executables): geometric mean
1.020; sum 83,980,983 to 86,515,519 bytes. Cedar +9.3% (+463 kB, one
program in three cases), L04 +2.7%, L17 +2.4%; the smallest growth is
+0.5%. In a first measurement on 12 object files of lean2rr programs
the growth was 1.6% to 25% of the object's `.text` (the 25% is a 70 kB
object that gains the same 16.8 kB).

**Other code: a correction (2026-11-19).** This entry said until
2026-11-19: "upstream's benchmark suite, core and std (33 units,
lowered MLIR): byte-identical with and without the patch". **That
sentence was wrong as a claim about the patch in the series.** It was
measured on pristine `36a55a0f` with 30-a alone, on a machine with
SVE. There MLIR's SVE storage pass ran first on every function, with
the same default configuration, and had already merged the blocks; the
vector pass found nothing left to merge. So 30-a alone looked neutral.
In lean2rr's series 28-a comes before 30-a, and upstream has 28-a
since #1099. Then the vector pass is the only block merger, on every
target, and the sentence does not hold.

The corrected facts, measured on upstream's main (`c2861a55`, which
has 28-a), MLIR's pass against the patch:

- **30 of the 33 units change in lowered MLIR** (more blocks: std
  21,574 to 28,789 blocks, mltt 6,333 to 18,266). The `Disabled` and
  the `Normal` form give identical output.
- **`.text` of the 33 units' objects:** 0.7% larger in the geometric
  mean, 2.1% in total (700,279 to 715,123 bytes). By unit: from 23%
  smaller to 11% larger. The largest growth is derive +11.4% and mltt
  +10.5%; 11 units do not change; four are smaller (list-membership
  -23%).
- **Run time of upstream's suite: not measured.**
- Upstream's SIMD tests (13 tests, two levels, two stages: 52 files):
  6 files differ (two tests, with blocks not merged); their LLVM IR at
  `-O aggressive` is identical.

The numbers of lean2rr's programs above stand (53 programs: `.text`
+2.0% in the geometric mean, the largest +9.3%; run time 1.000): they
were measured on the series, where 28-a is before 30-a.

The earlier comparison of 72 output files of upstream's tests (70
byte-identical, 2 identical after the random names of Rust modules
are made equal) was made in the same way, on pristine with 30-a alone
on the SVE machine, and has the same limit.

**Build time of other programs** (timing run 22, 2026-11-18; rrc and
the link from the `.rr`, every texture in a warm store on a memory
file system, the compilers in turn on each test; another agent's
builds ran on the machine, so CPU time was taken beside wall time):

| Compiler | per small test (20 tests, mean of two passes) | against the series of 12 | slower in |
|---|---:|---:|---:|
| the series of 12 patches | 1.684 s | - | - |
| with 31-a | 1.673 s | -0.011 s | 10 of 20 |
| with 32-a | 1.676 s | -0.008 s | 12 of 20 |
| with 31-a, 32-a and the amended 28-a and 29-a | 1.670 s | -0.014 s | 7 of 20 |
| with 30-a on top (the series of 15) | 1.832 s | +0.148 s (+9%) | 20 of 20 |

A second build of the compiler with 30-a, made the same way as the one
without it, confirms it: +0.172 s for each test, slower in 20 of 20.
So the cost is 30-a's alone.

Where the time goes (three tests, to each stage): not in MLIR, where
the stage is equal or faster with the patch. The module that goes to
LLVM is 18%, 18% and 48% larger, and the extra time is in LLVM's
optimization and code generation. The mechanism (blocks that MLIR no
longer merges are optimized and emitted by LLVM) is supported by these
stage times and sizes; it is not isolated further (no variant with
partial merging was built).

The two large programs (two runs each, the compilers in turn): lean-zip
37.62 s and 37.63 s without 30-a, 35.00 s and 36.94 s with it; Cedar
78.16 s and 83.27 s without, 76.38 s and 77.58 s with. So "not slower"
is what the data supports for large programs: there the merging that
the patch removes cost at least as much as LLVM's extra work.

**Run time of the whole series with 30-a** (timing run 22, a direct
step against native, 53 cases): 0.569, where the series without it had
0.568 in run 21.

**Not measured:** the exponential growth on a small input (not
reduced); a run of the JIT bridge; the build-time mechanism beyond the
stage times above.

**Repro.** [`repros/bug30-vector-lowering-merge.mlir`](repros/bug30-vector-lowering-merge.mlir) shows the mechanism through `reussir-opt`: MLIR's pass merges the arms of a function without a vector into blocks with arguments, and the pipeline's own pass leaves them (`run.sh` prints REPRODUCES or FIXED). It does not show the multiplication. In the gate on the series of 16 patches (2026-11-18): REPRODUCES on pristine `36a55a0f`, FIXED on the series.

## Upstream note

Pull request reussir#1100 is open (2026-11-19), in the `Normal` form
after the maintainer's review. The report gives the phase table and
the block-argument counts of the three variants. The MLIR behaviour (a
lowering pass for one dialect that simplifies the regions of all code)
is worth an LLVM report of its own, together with entry 28's.
