# 22. A wildcard arm over a wide enum costs N^3 code

## Summary

**Kind:** cost. **Status:** worked around (build time only; lean2rr
releases held wide values out of line in wildcard arms). No patch.

**Verdict: cost, not a bug.** Three documented Reussir design choices
multiply here; none is wrong by Reussir's rules: the pattern compiler and
codegen give an enum match one region per variant, so a wildcard arm is
copied into every constructor it covers (`semi/pattern.rs`, "Closed: one
subtree per variant"; `codegen/lower/expr.rs`, `ctor_switch`); the
ownership pass releases every held value in each copy, also on paths that
end in a panic; and `RcDecrementExpansion` with the first
`AcquireDropExpansion` expands the release of a value of unknown variant in
line, one level deep, as a match over its variants.

A wildcard arm over a wide enum is copied per constructor, with the
releases expanded in line in each copy: N^3 code. A derived `BEq` on 40
constructors took 9 minutes to build (round 6, PRG6-02).

## Symptom and repro

Repro [`repros/bug22-wildcard-wide-enum.py`](repros/bug22-wildcard-wide-enum.py)
`N OUT.rr [wild|sink|false]` (pure Reussir; prints `100`): the Reussir
analogue of a derived `BEq` on a recursive enum with N constructors, shaped
as lean2rr emitted it (a constructor-index test, then a match whose arm i
matches the second value against constructor i, with a `_ => unreach()`
default). `sink` adds lean2rr's workaround (below). In Lean: a derived
`BEq` on a recursive inductive with N constructors
(`adv6/programs/B30Beq.lean`, `B40Beq.lean`).

**Command.** `rrc OUT.rr -O aggressive`.

**Expected (lean2rr's expectation, not a Reussir promise).** Build time
about linear in N, as natively (about 1.3 s).

**Actual on ef922049.** For lean2rr's derived instances: N = 10, 20, 30,
40: 18, 26, 85, 536 s (BEq); DecidableEq N = 30: 493 s. The pure-Reussir
analogue: 1.2, 9.3, 65, 444 s. The `beq` function grows from 939 MLIR lines
at entry to 24k after TokenReuse at N = 10 (3.3k to 155k at N = 20); MLIR's
SCCP then takes about size^2.4 ([bug 11](11-sccp-call-graph.md)'s class).

## Cause

N outer arms × (N − 1) copies of the inner wildcard × an N-way in-line
release of each held field of the inductive's type = N^3.

## lean2rr

A wildcard arm covering two or more constructors releases the values of
wide enums (8 or more constructors) that it holds and does not use through
one out-of-line call (`l2r_sink`, `#[transform_anchor]` so the inliner does
not put the expansion back; Lower/Code, `sinkWildcardHeld`; a required
part in the registry): BEq N = 40 27 s, DecidableEq N = 30 21 s.

No patch: the possible upstream improvements are all missed optimizations
(one region for the constructors a wildcard covers; no releases on paths
that end in a panic; outlining the release of a wide enum in the first
expansion phase).
