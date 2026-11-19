# 28. On a target with SVE, rrc fails on a large function that has no vector

**Kind:** bug (valid code rejected). On an aarch64 target with SVE, rrc
runs MLIR's pass `arm-sve-legalize-vector-storage` on every function.
That pass fails on some large functions that have no vector at all, and
rrc stops with `lowering pipeline failed: RunPass` and no diagnostic.
Patch 28-a applies the same patterns without the cleanup that fails.

## Summary

**Kind:** bug. **Status:** patched (28-a), in the series on upstream
`36a55a0f` (Reussir branch `l2r-base13-r7`, tree `6dc99546`; the patch is the file `patches/28-a-sve-vector-storage-patterns.patch`).
lean2rr reaches the bug on the build machine (aarch64 with SVE): the
largest function of the row oracle of `tests/runtime/rows-check.sh`
does not compile without the patch. `scripts/l2r.py` requires the
patch on every host (it checks for the text
`createReussirLegalizeVectorStoragePass` in `lib/CAPI/Passes.cpp`), so
a missing patch gives a clear message, not `RunPass`.

**Upstream (2026-11-18):** Open at `36a55a0f`. New with upstream's
vector work (#994, #1008); `l2r-base12` does not have the pass. The
direct cause is in MLIR (LLVM 23.1.2), but Reussir schedules the pass
on every function, so the fix is in Reussir. Not reported to Reussir
(the maintainer takes fixes from this directory) and not reported to
LLVM. The patch applies to a clean `36a55a0f` alone.

## Context

- **The pass.** MLIR's `arm-sve-legalize-vector-storage` rewrites the
  stack storage of scalable vectors (predicate vectors need another
  storage type). rrc's pipeline runs it for each function when the
  target has SVE (`crates/reussir-backend/src/pipeline.rs:608`,
  `if options.arm_sve`; the pass is made in `lib/CAPI/Passes.cpp:271`).
- **The greedy driver.** MLIR applies a set of patterns with
  `applyPatternsGreedily`. With its default configuration the driver
  also folds operations, removes dead code and simplifies regions, in
  rounds, at most 10. If the function still changes after 10 rounds,
  the driver answers "failure".
- An x86-64 host, and an aarch64 host without SVE, never run the pass.

## Symptom and repro

**Through lean2rr** (the port's first gate, 2026-11-18):
`tests/runtime/rows-check.sh` stops with `rows-check: building the
oracle with lean2rr failed`. rrc exits 2 after about 35 s with only

```
ERROR reussir_backend::pipeline: lowering pipeline failed error=RunPass
```

With `-v`: `FAILED LegalizeVectorStorage on func.func
@...l_runNat___l2r_0____l2r__flat.borrowed_1`. That function has 6518
blocks, no memref and no vector. The failure is the same in every run,
also with one thread, with `--disable-borrow-analysis` and without
`--reuse-across-call`.

**Minimal repro, plain MLIR, no Reussir**
([`repros/bug28-sve-storage-chain.py`](repros/bug28-sve-storage-chain.py)
writes it for a chain length N): a chain of blocks, laid out last
block first, where each block passes its two arguments on, once in each
order.

```
func.func @chain(%p: i1, %c: i64) -> i64 {
  cf.br ^d0(%c, %c : i64, i64)
^dN(%vN: i64, %wN: i64):                 // the last block comes first
  %r = arith.addi %vN, %wN : i64
  return %r : i64
...
^d0(%v0: i64, %w0: i64):
  cf.cond_br %p, ^d1(%v0, %w0 : i64, i64), ^d1(%w0, %v0 : i64, i64)
}
```

Stock `mlir-opt --arm-sve-legalize-vector-storage` (LLVM 23): exit 0
for N = 3, 7, 8; exit 1 with no message for N = 9, 10, 11, 12, 20.
`mlir-opt --canonicalize` on N = 12: exit 0.

There is no plain `.rr` repro: given to rrc as MLIR, the chain is
cleaned by earlier passes before it reaches the SVE pass. The chain
appears only after the lowering to branches.

## Cause

MLIR's pass calls `applyPatternsGreedily` with the default
configuration and signals a pass failure when the driver answers
"failure". The answer means "no fixpoint after 10 rounds", and the
rounds are spent on region simplification, not on the storage patterns:
the step that drops redundant block arguments goes over the blocks once
for each round, in layout order. When a block's arguments become
redundant only after a block that comes later in the layout is cleaned,
each round cleans one block. A chain of 9 such blocks needs more than
10 rounds.

Checked on the function that lean2rr's program fails on (dumped before
the pass): the driver with no pattern at all and aggressive region
simplification fails with 10 rounds and passes with 11; with normal or
no region simplification 10 rounds pass. The pass has no option for the
driver's configuration.

## lean2rr

lean2rr emits no vector code, so the pass has nothing to do in its
programs. A large generated function can still fail on an aarch64 host
with SVE. In the port's first gate, one program of all (747 runtime
tests, 54 corpus builds, the raytracer, the check scripts) failed: the
row oracle, whose `runNat` is the largest single function. With 28-a
the oracle builds and `rows-check.sh` prints `rows-check: every row
agrees` (13 rows files, 5488 rows).

## Patch

[`patches/28-a-sve-vector-storage-patterns.patch`](patches/28-a-sve-vector-storage-patterns.patch),
`[conversion] legalize the storage of scalable vectors with the patterns
alone` (11 files, +156/-4).

- A new pass, `reussir-legalize-vector-storage`
  (`lib/Conversion/LegalizeVectorStorage/`), applies MLIR's own patterns
  (`populateLegalizeVectorStoragePatterns`) with folding, constant CSE
  and region simplification off. If the patterns themselves do not reach
  a fixpoint, that is still an error.
- Like MLIR's pass, it fails when a use of a legalized allocation is
  left that the patterns cannot rewrite, with a diagnostic at the
  allocation: `the storage of a scalable vector is used by an operation
  that cannot be legalized`.
- The C API's constructor that the pipeline calls
  (`reussirCreateArmSVELegalizeVectorStoragePass`) returns the new
  pass; `reussir-opt` registers it; the vector lowering test uses it.
- Amended on 2026-11-18, one line: the JIT bridge
  (`lib/Bridge/Bridge.cppm`) added MLIR's pass in its own lowering
  pipeline too, and the first form of the patch had missed it (the
  search did not include `.cppm` files). The bridge now adds the new
  pass. That line is compiled and linked, not executed: nothing in the
  tree calls the bridge, and rrc and rrepl use the Rust pipeline. So
  lean2rr was not affected by the gap.

Two smaller ways were looked at and do not work. A canonicalize before
the pass has the same limit of 10 rounds (it only does not report it),
so a longer chain still fails. To skip functions without vectors leaves
a large function with a vector failing.

**Tests.** `conversion/legalize_vector_storage.mlir`, two cases: the
chain with N = 10 (MLIR's pass: exit 1; the new pass: passes), and a
predicate slot that escapes into a call (the expected error).
`conversion/vector_lowering.mlir` uses the new pass.

## Review

One round by an independent reviewer with one required change (local
notes `port13/reviews/RV4`, round 3). The reviewer reproduced the
failure with stock `mlir-opt` and on the dumped function, and agreed
with the cause and with a replacement pass as the smallest correct fix.
The finding: the first version dropped MLIR's check for a use that is
left over, and such a use was not caught later, against what the
patch's notes said (a slot of the wrong vector type went through with
exit 0). The patch now has the check and its test. The same greedy
call with the default configuration is in two more upstream passes
(`SpecialPointerTag.cpp`, `ClosureBetaReduction.cpp`); they run early,
on structured code, and no failing program is known. Not changed.

Not run: the full lit suite, the sanitizer tests. The patch's changed
lines are clean under clang-format 23.1.0 (LLVM style) since
2026-11-19; the formatter moved line breaks in 4 lines and changed no
token.

## Measured claim

What the patch buys: the function compiles. What it costs in generated
code: nothing that was measured. No wall-time comparison was made.

| Check | Result |
|---|---|
| `rows-check.sh` through lean2rr, final series | fails without 28-a (the gate's log), `every row agrees` with it |
| upstream's vector lit tests (`simd`, `vector`, `legalize`, `swizzle`, `sve`) | 20 of 20 pass |
| 13 `frontend/simd_*.rr` and 5 tests without vectors, `-O none` and `-O aggressive`, lowered MLIR and LLVM IR (72 files), pristine against patched | 70 byte-identical; 2 identical after the random names of Rust modules are made equal |
| upstream's benchmark suite, core and std (33 units), lowered MLIR, pristine against patched | 33 of 33 byte-identical |
| 14 lean2rr programs, the series without and with 28-a | 13 identical function by function; the 14th has one function with the same instructions and another block order, a difference that the same compiler shows from run to run; its object file is byte-identical |
| time in the pass over the 836 functions of the row oracle (`-v`, one thread) | 1139 ms before (the failing run), 85 ms after |

The last row was measured on the first version of the patch, before the
check for a left-over use and the constant CSE switch were added; it
was not measured again. On an SVE target the old pass gave every
function one more round of folding and block merging; no measured unit
shows a difference, but a program could.

## Upstream note

Not reported. A report to Reussir would give the minimal MLIR chain and
the two `mlir-opt` lines. The MLIR behaviour (a legalization pass that
fails on the limit of an unrelated cleanup) is worth an LLVM report of
its own; none is filed.
