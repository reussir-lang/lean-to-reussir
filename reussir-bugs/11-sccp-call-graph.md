# 11. Interprocedural SCCP is superlinear on large call graphs

## Summary

**Kind:** cost (stock MLIR pass). **Status:** open (build time only). No
patch.

**Verdict: cost of a stock MLIR pass, not a Reussir defect.** The pipeline
runs MLIR's own `createSCCPPass` (`crates/reussir-backend/src/pipeline.rs`),
quadratic in the number of call sites by its algorithm; Reussir promises
nothing linear. The towers first blamed on it were
[bug 20](20-statet-tower.md).

MLIR's interprocedural SCCP takes superlinear time on large call graphs.
Large lean2rr programs (thousands of functions) spend most of their build
there.

## Symptom and repro

Repro [`repros/bug11-sccp-call-graph.py`](repros/bug11-sccp-call-graph.py)
`N OUT.rr` writes N self-recursive functions (so they are not inlined)
that each call the same function `g`, and a function that calls all N. It
prints one number.

**Command.** `rrc OUT.rr -O aggressive`.

**Expected.** Build time about linear in N.

**Actual on ef922049** (rrc build time, several runs on the loaded test
machine; a build of N = 10 takes 0.3 s):

| N | build |
|---|---|
| 1000 | 1.6-2.4 s |
| 2000 | 3.4-6.5 s |
| 4000 | 10-31 s |

In every run N = 4000 took 2.9-4.8 times as long as N = 2000.

perf puts the time in MLIR's data-flow solver
(`DeadCodeAnalysis::visitCallableTerminator`,
`AbstractSparseForwardDataFlowAnalysis::visitCallableOperation`, and the
lookups of analysis states).

Sizes that hit the limits (lean2rr outputs, with `--no-closure-wpd`): five
transformer towers in one program (`Cn3PolyM1`, 2140 functions) build in
936 s and 7.5 GB and give the right output. A single growing `StateT` tower
used at `IO` (8 lines of Lean) does not build within 30 minutes or 12-15
GB; the same tower at `Id` builds in 60 s.

A Std.Http program (round 6, `adv6/io/Io6Http.lean`, a local HTTP server
and TCP clients; lean2rr's output has 17,197 functions and 8241
polymorphic-FFI instances), built with patch 0017
([bug 23](23-polyffi-link.md)), reaches the MLIR lowering pipeline after 12
minutes of texture compiles and a 6 s link. perf sampled 31 minutes into
the pipeline: all of the time in interprocedural SCCP
(`DeadCodeAnalysis::visitCallableTerminator`, the data-flow solver's state
lookups), 7 GB. It was stopped 51 minutes into the pipeline, unfinished.

## Cause

`mlir::createSCCPPass` runs on the whole module twice
(`crates/reussir-backend/src/pipeline.rs`, through `reussirCreateSCCPPass`
in `lib/CAPI/Passes.cpp`). It is interprocedural: every change of a
callable's argument or return lattice re-visits the callable's terminators
and all of its call sites. lean2rr's uniform code for polymorphic
recursion has large, heavily shared callees (the conversion and
application functions of its function and `Box` representations).

## lean2rr

No workaround of its own. The tower programs above were mostly bug 20:
rrc's inliner multiplied lean2rr's conversion code, and SCCP then iterated
over the result. With bug 20 worked around (lean2rr keeps those functions
out of the inliner), `Cn3PolyM1` builds in 70 s and 1.5 GB (the whole
build, lean2rr included) and the `StateT` tower at `IO` in 21 s and 0.4 GB,
so the programs it was blamed for build in acceptable time. One
representation shared by all uniform function types (every
`Box`-mentioning function type one enum, applied with boxed arguments,
`lean_apply`-style) was tried and measured: it removes most of the
conversions, but its single application function, an arm for every target
of the uniform code, is a hub through which SCCP and the decrement
expansion of the arguments cost more than they save (`Cn3PolyS1` 649 s and
5.7 GB against 115 s and 2 GB without it).
