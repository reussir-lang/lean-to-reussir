# 20. The MLIR inliner grows lean2rr's conversion code exponentially

## Summary

**Kind:** unclear. **Status:** worked around (build time only; lean2rr
keeps its conversion, unboxing and uniform-code application functions out
of rrc's inliner). No patch.

**Verdict: unclear.** Keeping lean2rr's conversion functions out of the
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
missing feature).

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
