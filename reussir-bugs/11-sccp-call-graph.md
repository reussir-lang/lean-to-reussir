# 11. Interprocedural SCCP is superlinear on large call graphs

**Kind:** cost (build time), in both parts: the superlinear SCCP of a stock
MLIR pass, and 11b, quadratic glue lookups in Reussir's own code. Not a
bug: rrc's output is correct; the blowup can make large builds infeasible
(time or memory), and patches 11-a and 11-b are optimizations.

## Summary

**Kind:** cost (stock MLIR pass), with a small local optimization; plus a
cost in Reussir's own code (11b, build time; first classed as a bug,
reclassified on 2026-10-05 because the output is correct). **Status:**
patched (11-a for SCCP, 11-b for 11b), applied in `./reussir` (`l2r-local`
cc8e5aa5).

**Verdict: cost of a stock MLIR pass, not a Reussir defect.** The pipeline
runs MLIR's own `createSCCPPass` (`crates/reussir-backend/src/pipeline.rs`),
whose time is superlinear in the number of call sites (measured, below:
doubling N costs 2.9-4.8x; [issue 22](22-wildcard-wide-enum.md) measures
about size^2.4 on one large function; no bound from MLIR's documentation
is known here); Reussir promises nothing linear. The towers first blamed
on it were
[issue 20](20-statet-tower.md). Under the policy's third refinement
(fixable build-time costs get a small patch), 11-a runs SCCP across calls
only within a budget of call sites. Building the Std.Http program once
SCCP was fixed exposed **11b**, a real quadratic in Reussir's own code:
the acquire/drop expansion built a symbol table of the whole module for
every glue lookup; 11-b fixes it.

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
polymorphic-FFI instances), built with patch 23-a
([issue 23](23-polyffi-link.md)), reaches the MLIR lowering pipeline after 12
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

No workaround of its own. The tower programs above were mostly issue 20:
rrc's inliner multiplied lean2rr's conversion code, and SCCP then iterated
over the result. With issue 20 worked around (lean2rr keeps those functions
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

## Patch

### 11-a: SCCP across calls only within a budget

Patch file
[`patches/11-a-sccp-call-budget.patch`](patches/11-a-sccp-call-budget.patch)
(`l2r-local` commit `ac70115a`, applied in `./reussir`; `l2r-local` head
cc8e5aa5).

Where the cost comes from: each time MLIR's data-flow framework finds one
more call site of a function, or the arguments at one change, it visits
the function again and walks all its known call sites
(`DeadCodeAnalysis::visitCallableTerminator` adds the function's returns
as predecessors of each call,
`AbstractSparseForwardDataFlowAnalysis::visitCallableOperation` joins each
call's arguments into the function's), so the cost follows the sum over
callees of the square of their call sites.

The patch adds a pass `reussir-sccp` (`lib/Transformation/SCCP/SCCP.cpp`),
which the C API's SCCP factory (`reussirCreateSCCPPass`, used twice by the
pipeline) now returns. It counts the call sites of every callee that has a
body and runs the stock `sccp` on the whole module when the sum of their
squares is at most `max-call-site-pairs` (2^22), and nested on each
`func.func` otherwise:

```c++
module.walk([&](mlir::CallOpInterface call) {
  ...  // skip a callee without a body (an FFI import, a runtime function)
  uint64_t &count = callSites[callee];
  pairs += 2 * count + 1;       // the n-th site adds n^2 - (n-1)^2
  ++count;
});
mlir::OpPassManager pipeline(mlir::ModuleOp::getOperationName());
if (pairs <= maxCallSitePairs)
  pipeline.addPass(mlir::createSCCPPass());
else
  pipeline.addNestedPass<mlir::func::FuncOp>(mlir::createSCCPPass());
```

**Why it is correct.** SCCP on one function is the same stock pass with a
smaller scope: a `func.func` as the analysis root makes every callee
external, so call results and the entry block's arguments start
overdefined and nothing is assumed about callers. It only finds fewer
constants; LLVM's IPSCCP still propagates across calls later. Programs
under the budget are compiled exactly as before (lean2rr's classic corpus
has at most 1.5M pairs).

**Verification.** Test `conversion/sccp_call_site_budget.mlir`. Repro
(`run.sh`, final stack): `issue 11   FIXED       N = 2000: 13.7 s, N =
4000: 23.4 s, N = 10: 1.6 s (1.80x without the fixed cost, for twice the
call sites)` (unpatched: 2.9-4.8x). The Std.Http program (335M pairs)
gets SCCP per function: 3 s and 19 s for the two runs.

### 11-b (issue 11b): glue looked up in symbol tables built once

Patch file
[`patches/11-b-glue-symbol-tables.patch`](patches/11-b-glue-symbol-tables.patch)
(`l2r-local` commit `5e0273b2`).

**The cost.** `createDtorIfNotExists` and
`emitOwnershipAcquisitionFuncIfNotExists` (`lib/IR/ReussirOps.cpp`) built
a new `mlir::SymbolTable` of the whole module on every call, to look up
the glue function of a record type, and the acquire/drop expansion calls
them for every `ref.drop`/`ref.acquire` of a named record it outlines:
time quadratic in the size of the module. Found by building the Std.Http
program once its SCCP was fixed: the second acquire/drop expansion ran
for more than 45 minutes, 90% of the time in `SymbolTable::SymbolTable`
(perf).

**The fix.** Both helpers take an optional `mlir::SymbolTableCollection`,
look the glue up in it and add the functions they create (the drop glue,
the drain declaration, the acquire glue). The acquire/drop expansion
builds one collection per run and passes it through its patterns. The
outlined acquire glue of a record creates, while its body is built, the
glue of its named `[value]` members ([bug 19](19-cell-of-value-record.md),
19-a); `emitOwnershipAcquisition` passes the collection on to that
creation too. Other callers keep building a table per call.

**Why it is correct.** The same functions are found and created; only
the lookup changes. Functions are never erased during the pass
(`func.func` is not trivially dead), so the collection holds no dangling
entries, and every function the pass creates is entered in it.

**Verification.** Test `frontend/cell_value_record_glue_order` (a
`Cell<Pair>` read before a `Cell<Quad>`, RV8C-01 below). With 11-a and
11-b the Std.Http program builds to an object: 26 minutes of MLIR passes,
the second acquire/drop expansion 84 s.

### Review

Round RV8C (local review notes, patches 22-a, 17-a, 11-a, 11-b, 20-a
and 16-a):

- 11-a held (Q3): per-function SCCP is sound and safe in parallel, the
  budget arithmetic is right and deterministic, and under the budget the
  stock pass runs unchanged (identical IR for four corpus programs).
  **RV8C-04** (low, optimization loss): the budget counted call sites of
  declarations, which cost the analysis nothing. Resolved in the final
  11-a: only callees with a body count.
- 11-b held on its own (Q4). **RV8C-01** (medium): composed with 19-a
  (bug 19), the member glue that 19-a's outlined acquire glue creates
  bypassed the collection, so a later lookup missed it and rrc failed
  with "redefinition of symbol" (a `Cell<Pair>` read before a
  `Cell<Quad>`). Resolved in the final 11-b: the collection is threaded
  through `emitOwnershipAcquisition`; the reviewer's repro is the new
  test. **RV8C-02** (textual conflicts with the ten patches from 08-a to
  27-a of the series): resolved by rebasing the six patches of the round
  onto them.

**Effect on lean2rr.** Build time only. Programs under the budget are
compiled exactly as before; very large programs (the Std.Http program,
17,197 functions) now build.

## Upstream note

The pipeline's interprocedural `sccp` is quadratic in the call sites of a
callable (the data-flow framework revisits a function and walks all its
call sites at every change); a module with one function called from 4000
places spends 7 s there, a 17,000-function program over 50 minutes. A
budget on the sum of squared call sites, falling back to per-function
SCCP, avoids it. Separately, `createDtorIfNotExists` and
`emitOwnershipAcquisitionFuncIfNotExists` build a `SymbolTable` of the
whole module per call; a `SymbolTableCollection` per pass run removes the
quadratic.

