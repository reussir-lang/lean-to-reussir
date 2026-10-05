# 20. The MLIR inliner grows lean2rr's conversion code superlinearly (build time)

**Kind:** cost (build time and memory of the MLIR inliner; first unclear,
cause found later). Not a bug: rrc's output is correct; patch 0034 is an
optimization.

## Summary

**Kind:** unclear at first; found later to be a growth of the MLIR
inliner's chains of copied calls (a cost), with a small local
optimization. **Status:** patched (0034), applied in `./reussir`
(`l2r-local` cc8e5aa5); lean2rr also works around it (it keeps its
conversion, unboxing and uniform-code application functions out of rrc's
inliner), and keeps doing so.

With lean2rr's conversion, unboxing and application functions inlinable,
rrc's build time and memory on polymorphic recursion through monad
transformers grow far faster than the program (superlinearly; the shape of
the growth was not measured).

**Verdict (first): unclear.** Keeping lean2rr's conversion functions out of the
MLIR inliner cuts build time and memory about five-fold, but the inliner is
not shown to misbehave: there are no operation counts before and after
inlining, and the growth was never measured as exponential (the inliner's
description claims bounded growth: one iteration, callees of at most 256
operations). Reussir does not promise the same build time with and without
inlining. `#[transform_anchor]` exists for transform-dialect scripts;
codegen adds `no_inline` only so that the anchor survives, so lean2rr
relies on a side effect (pinned by Reussir's test
`tests/integration/frontend/inline_transform.rr`; LLVM still inlines
anchored functions). A plain no-inline attribute would be the clean way (a
missing feature). The cause was found later (0034, below): within its one
iteration, MLIR's inliner also inlines the calls an inlining copies in, so
a call into a recursive group of functions gets every chain of distinct
members inlined.

## Symptom and repro

Repro [`repros/bug20-statet-tower.lean`](repros/bug20-statet-tower.lean),
built through lean2rr with its workaround turned off
(`L2R_NO_INLINE_ANCHORS=1` in lean2rr's environment):

```
def nestS {m : Type → Type} [Monad m] : Nat → m Nat
  | 0 => pure 0
  | n+1 => do
    let r ← (nestS (m := StateT Nat m) n).run' n
    pure (r + 1)
def main (args : List String) : IO Unit := do
  IO.println s!"S {Id.run (nestS (args.length + 5))}"
```

Polymorphic recursion through `StateT`: lean2rr makes a uniform instance of
`nestS` and a few typed ones, with many representations of the same
function types (`Nat → Box`, `Box → Box`, `Nat → Nat → Box`, ...), the
wrapper variants that convert between them, and the unboxing functions of
`Box`. Prints `S 5`.

**Command.** `scripts/l2r.py` with lean2rr's flags (`run.sh` measures rrc
alone), with and without `L2R_NO_INLINE_ANCHORS=1`.

**Expected (lean2rr's expectation, not a Reussir promise).** About the same
build time and memory with and without, as for the same program compiled
natively (3 s).

**Actual on 42635042** (the eight-patch set, see
[the builds](README.md#builds-named-in-the-entries); rrc to an object file,
this machine; times on a loaded host):
115-182 s and 2.0-2.9 GB without the workaround, 27 s and 0.5 GB with it.
Sizes that hit the limits: the same tower used at `IO` (adv4 `St4PolyP1a`,
8 lines) did not build within 30 minutes or 15 GB (rrc killed or out of
memory); five towers in one program (`Cn3PolyM1`) took 715-936 s and
7.3-7.5 GB.

## Cause

Not narrowed down to the inliner's code. rrc's `reussir-default-inliner`
(MLIR's SCC inliner, one iteration, callees of at most 256 operations) runs
before every other optimization. Marking functions `#[transform_anchor]`,
which keeps them out of that inliner and nothing else, removes the growth:

- with lean2rr's conversions (`l2r_fconv_*`), unboxing functions
  (`l2r_unbox_*`) and the application functions of types with wrapped
  values out of it, `St4PolyP1a` builds in 26 s and 0.4 GB (rrc alone);
- with the application functions of the `Box`-mentioning function types
  out as well, four towers in one program (`Cn3PolyScalar`) build in 93 s
  and 2 GB instead of 216 s and 4.5 GB;
- with only the conversions and function unboxing out, `St4PolyP1a` takes
  134 s and 2 GB;
- with only the application functions out, it does not build within
  400 s;
- with `-O none` (no inliner) it builds in 18 s.

A perf profile of the unpatched build is mostly MLIR's SCCP data-flow
solver, canonicalization and region simplification over the inlined code.
These functions call each other: an unboxing function converts what a
`Box` holds from every representation it may hold, a conversion converts
from the wrapped representation, an application of a wrapped value applies
it at its own representation; a small synthetic cycle of mutually calling
functions (each calling the next two) does not grow, so the trigger is
more specific than a cycle of small functions.

## lean2rr

It marks these functions, and the application functions of the function
types of uniform code (those that mention `Box`), `#[transform_anchor]`
(`Lower/Finish.lean`, `anchoredFns`; plan §5.3). LLVM still inlines them
after Reussir's passes. The towers of the adversarial rounds build in 15 s
to 2.5 minutes and at most 3 GB, the whole build (`St4PolyP1a`: 21 s,
0.4 GB; `Cn3PolyM1`: 70 s, 1.5 GB). `run.sh` builds the repro with
`L2R_NO_INLINE_ANCHORS=1` and without: 136 s and 2.9 GB against 18 s and
0.3 GB (rrc, to an executable).

## Patch

Patch file
[`patches/0034-l2r-local-bug-20-do-not-inline-a-copied-call-into-a-.patch`](patches/0034-l2r-local-bug-20-do-not-inline-a-copied-call-into-a-.patch)
(`l2r-local` commit `ac5d1d85`, applied in `./reussir`; `l2r-local` head
cc8e5aa5).

**What was found.** The default inliner runs MLIR's SCC inliner for one
iteration with a cap of 256 operations on callees, and its description
says this unrolls recursion one level. But within the iteration MLIR's
inliner also inlines the calls that an inlining copies into the caller,
and stops a chain only when a callee repeats on it (its inline history).
A call into a recursive SCC thus got every chain of distinct members of
the SCC inlined, a growth that multiplies the fan-out of the SCC along
each chain. lean2rr's conversions, unboxing and application functions
call each other this way: on the repro (without lean2rr's workaround) the
module grew from 16,980 operations to 190,318 in the inliner, through
4792 inlines of which 3833 were of copied calls (2326 into recursive
callees).

**The change** (`lib/Transformation/DefaultInliner/DefaultInliner.cpp`):
before inlining, every call is marked with the name of the function it is
written in (`reussir.inliner_home`, removed afterwards), the callables on a
cycle of the call graph are collected (`llvm::scc_begin` over MLIR's
`CallGraph`, `hasCycle()`), and the profitability check refuses a copied
call (marked with another function) whose callee is recursive:

```c++
config, [&](const mlir::Inliner::ResolvedCall &call) {
  if (!calleeIsSmall(call.targetNode->getCallableRegion(), maxCalleeOps))
    return false;
  mlir::CallOpInterface callOp = call.call;
  return !recursive.contains(call.targetNode) ||
         !copiedByInlining(callOp.getOperation());
});
```

Calls the program wrote are inlined as before, so recursion unrolls one
level, and a copied call into a non-recursive callee is inlined as before.
The pass is also registered in `reussir-opt`.

**Why it is correct.** It only declines some inlinings; a call that is
not inlined stays a call to the same function, so the program is the
same. The mark survives cloning (attributes are cloned) and moving, and
is removed after inlining on both the success and the failure path.

**Verification.** Test `conversion/default_inliner_recursive_scc.mlir`
(fails without the rule: more copies of the SCC's members). The tower
without lean2rr's workaround: 16,980 -> 67,238 operations after the
inliner; rrc 236 s, 1.8 GB -> 70 s, 0.98 GB (through `l2r.py`, back to
back, loaded machine, the series 0030-0035). With the workaround, peak
memory is unchanged (226 MB).

`run.sh` on the final stack: `rrc: 78 s, 770 MB; with the conversion
functions kept out of the inliner: 45 s, 217 MB (3.53x memory)` (before:
2.9 GB against 0.3 GB, about 10x). What remains is the inliner's ordinary
one-level inlining of the calls the program writes, which lean2rr's
anchors still avoid. `run.sh`'s first thresholds (FIXED at most 1.5x)
expected the anchors to stop mattering; they are now REPRODUCES at least
6x (the chains of copied calls) and FIXED at most 4.5x, so the line above
reads `FIXED`. lean2rr keeps its anchors: 3.5x less memory on this program
is worth keeping.

**Review.** Round RV8C (local review notes,
Q5): no defect. Recursion is computed on MLIR's `CallGraph` (every
top-level callable hangs off the external node, so the SCC walk reaches
all, and `hasCycle()` includes self-loops). Gaps, performance only:
recursion through closures or indirect calls is not seen, and calls
created by canonicalization count as written. Attribution with snapshots:
the patch changes HigherOrder (LLVM IR 195k -> 165k lines, call sites
15,762 -> 13,346), TypeclassGeneric (-0.1%) and Binarytrees (+0.3%) of the
classic corpus, with identical output and the same benchmark times within
noise.

**Effect on lean2rr.** With its anchors (as lean2rr builds), unchanged
memory; slightly different inlining on some corpus programs (above),
same output.

## Upstream note

`reussir-default-inliner` promises one level of recursion unrolling, but
MLIR's inliner, within one iteration, also inlines calls copied in by an
inlining until a callee repeats on the chain, so a call into a recursive
SCC inlines every chain of distinct members (a lean2rr module: 16,980 ->
190,318 operations). Refusing to inline a copied call whose callee is on
a cycle (tagging calls with their home function) restores the intent
(-> 67,238).

