# 24. The matrix-exponentiation pass emits different code from run to run

## Summary

**Kind:** bug (non-reproducible builds). **Status:** patched (0026),
applied in `./reussir` (`l2r-local` cc8e5aa5).

**Verdict: bug.** Reussir's LLVM pass that turns linear recurrences into
matrix exponentiation (`LinearRecurrenceMatExpPass`) collects the state of a
loop by iterating a hash map keyed by pointers, so the order of the state,
and with it the emitted code, follows heap addresses. The same input gives
different, equivalent modules from one run to the next. A compiler is
expected to be deterministic: build outputs cannot be compared or cached,
and a diff of two builds shows changes that are not there. The values
computed are the same.

## Symptom and repro

Repro [`repros/bug24-matexp-state-order.sh`](repros/bug24-matexp-state-order.sh)
`REUSSIR_CHECKOUT [RUNS]` runs the checkout's `reussir-llvm-opt` RUNS times
(default 12) on Reussir's own test input
`tests/integration/llvmpass/linear_recurrence_order6_e2e.ll` (an order-6
linear recurrence) through the O2 linear-recurrence pipeline, and counts
the distinct outputs.

**Command.** `reussir-llvm-opt --linear-recurrence-pipeline=O2
linear_recurrence_order6_e2e.ll -o OUT`, repeated.

**Expected.** One output.

**Actual on ef922049** (here 91da4f80, which does not touch the pass): 10
and 11 distinct outputs in two sets of 12 runs. `run.sh` prints
`issue 24   REPRODUCES  12 runs of the order-6 recurrence: 11 different
outputs`. Other measurements (review rv7/p22, round 1 and 2): rrc `-O
default --emit llvm-ir` on Reussir's frontend test
`per_ctor_box_sizing_mixed_arms.rr`, two different modules in 8 runs; the
pass alone on `linear_recurrence_matexp.ll` (Fibonacci), 2 outputs in 12
runs, and 1 in 30 runs with address-space randomization off (`setarch -R`);
the order-6 recurrence through the O2 pipeline, up to 19 outputs in 20
runs. The difference is a permutation of the state: for the Fibonacci loop,
two companion-matrix entries swapped (`mul %acc, 1` and `mul %acc, 0`).

Found while comparing rrc builds for the patches of issue 10 and bug 19
(agent B, `morepatches-b/`), and pinned to its cause by the review of those
patches (rv7/p22, round 1, finding RV7P-03).

## Cause

`LinearRecurrenceMatExpPass`
(`lib/LLVMPass/LinearRecurrence/LinearRecurrenceMatExp.cpp`) decomposes each
live-out value and each PHI update of a loop into an affine expression
(`AffineExpr`), whose coefficients are a `DenseMap<PHINode *, APInt>`
(`coeffs`, line 97). `analyzeLoop` builds the loop's state, a
`SetVector<PHINode *> statePhis`, by iterating those maps:

```c++
for (Instruction *liveOut : liveOuts) {
  auto expr = decomposer.decompose(liveOut);
  ...
  for (const auto &[phi, coeff] : expr->coeffs)
    statePhis.insert(phi);
}
...
    for (const auto &[usedPhi, coeff] : update->coeffs)
      statePhis.insert(usedPhi);
```

A `DenseMap` keyed by pointers iterates in an order that follows the
pointers' hashes, that is, heap addresses, which address-space
randomization and allocation history change between runs. The order of
`statePhis` is the order of the rows and columns of the companion matrix
and of the code that applies it (`emitAffine`), so it decides the output.
Every order gives the same values.

## lean2rr

No effect seen: lean2rr's runtime tests RtNat, RtHashMap and RtJpChain,
built three times each, gave identical LLVM IR (review rv7/p22); none of
them has a loop the pass transforms. A lean2rr program with such a loop
(a counting loop with several accumulators) would get equivalent code that
differs between builds. No workaround needed.

## Patch

Patch file
[`patches/0026-l2r-local-bug-24-order-the-matrix-exponentiation-sta.patch`](patches/0026-l2r-local-bug-24-order-the-matrix-exponentiation-sta.patch)
(`l2r-local` commit `d3d6688b`; applied in `./reussir`, `l2r-local`
cc8e5aa5). The state PHIs an expression uses are added in the order of the
loop header's PHIs:

```c++
+  auto addUsedPhis = [&](const AffineExpr &expr) {
+    for (PHINode &phi : header->phis())
+      if (expr.coeffs.contains(&phi))
+        statePhis.insert(&phi);
+  };
   for (Instruction *liveOut : liveOuts) {
     ...
-    for (const auto &[phi, coeff] : expr->coeffs)
-      statePhis.insert(phi);
+    addUsedPhis(*expr);
   }
   ...
-    for (const auto &[usedPhi, coeff] : update->coeffs)
-      statePhis.insert(usedPhi);
+    addUsedPhis(*update);
```

**Why it is correct.** Each expression adds the same set of PHIs as before
(those in its `coeffs`); only the order changes, and the order of the
header's PHIs is fixed by the input. The rest of the pass works on the state
in whatever order it gets, as it did for the orders the hash map produced
before.

**Verification.**

- New test `tests/integration/llvmpass/linear_recurrence_matexp_deterministic.ll`:
  the order-6 recurrence six times and the Fibonacci loop eight times
  through the pass, every output identical. It fails without the patch.
- `run.sh`: `issue 24   FIXED       12 runs of the order-6 recurrence: 1
  output`.

**Review.** Round 2 of the review of agent B's patches (rv7/p22/round2),
no defect:

- Deterministic: 20 runs each of the pass alone and of the O2 pipeline on
  five inputs (`linear_recurrence_matexp`, `_matexp_exec`, `_order6_e2e`,
  `_order4_e2e`, `_full_e2e`) gave one output each (the unpatched pass: up
  to 19 in 20 runs). rrc on `per_ctor_box_sizing_mixed_arms.rr`: one output
  in 10 runs at `-O default` and 6 at `-O aggressive`. No other
  pointer-ordered iteration in the pass affects the output.
- Values unchanged: every distinct output, the unpatched variants and the
  patched one, was linked with a driver and run under `lli` against the
  untransformed input (Fibonacci, an LCG and a quadratic recurrence for
  n = 0..399 and larger n up to about 8M; the order-4 and order-6
  recurrences up to n = 25): all agree.

**Effect on lean2rr.** None on the code's meaning; builds that use the
pass become reproducible.

## Upstream note

`LinearRecurrenceMatExp.cpp`, `analyzeLoop`, fills `statePhis` by iterating
`AffineExpr::coeffs`, a `DenseMap<PHINode *, APInt>`, so the state order
(the companion matrix's rows and columns, and the emitted code) follows
heap addresses: different output from run to run (10 distinct modules in 12
runs on `linear_recurrence_order6_e2e.ll`). Fix: add the used PHIs in the
order of `header->phis()`.
