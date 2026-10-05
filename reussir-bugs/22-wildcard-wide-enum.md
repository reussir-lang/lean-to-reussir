# 22. A wildcard arm over a wide enum costs N^3 code

**Kind:** cost (build time). Not a bug: rrc's output is correct; patch 0030
is an optimization.

## Summary

**Kind:** cost. **Status:** patched (0030, a build-time optimization),
applied in `./reussir` (`l2r-local` cc8e5aa5); lean2rr also works around
it (it releases held wide values out of line in wildcard arms).

**Verdict: cost, not a bug.** Three documented Reussir design choices
multiply here; none is wrong by Reussir's rules: the pattern compiler and
codegen give an enum match one region per variant, so a wildcard arm is
copied into every constructor it covers (`semi/pattern.rs`, "Closed: one
subtree per variant"; `codegen/lower/expr.rs`, `ctor_switch`); the
ownership pass releases, in each copy, every held value that copy does not
use, also on paths that end in a panic; and `RcDecrementExpansion` with the first
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
SCCP then takes about size^2.4 ([issue 11](11-sccp-call-graph.md)'s class).

With 0030 (the pure-Reussir analogue, `rrc -O aggressive` to an executable,
loaded machine): N = 10: 1.7 s -> 0.6 s; N = 20: 15.0 s -> 1.8 s; N = 30:
136 s -> 3.7 s; N = 40: 444 s (before, from above) -> 7.8 s; the same
output (`100`). `run.sh` does not run this repro (its generator is run by
hand).

## Cause

N outer arms × (N − 1) copies of the inner wildcard × an N-way in-line
release of each held field of the inductive's type = N^3.

## lean2rr

A wildcard arm covering two or more constructors releases the values of
wide enums (8 or more constructors) that it holds and does not use through
one out-of-line call (`l2r_sink`, `#[transform_anchor]` so the inliner does
not put the expansion back; Lower/Code, `sinkWildcardHeld`; a required
part in the registry): BEq N = 40 27 s, DecidableEq N = 30 21 s.

lean2rr keeps `l2r_sink` with 0030 applied (README policy: workarounds
stay, so that lean2rr also works with an unpatched Reussir).

Of the possible improvements (one region for the constructors a wildcard
covers; no releases on paths that end in a panic; outlining the release of
a wide enum in the first expansion phase), 0030 does the first.

## Patch

Patch file
[`patches/0030-l2r-local-bug-22-merge-the-copies-of-a-wildcard-arm-.patch`](patches/0030-l2r-local-bug-22-merge-the-copies-of-a-wildcard-arm-.patch)
(`l2r-local` commit `bc4aca4b`, applied in `./reussir`; `l2r-local` head
`cc8e5aa5`), rebased onto 0018-0027 and 0040 for the final stack, with the
change of review finding RV8C-03 (below).

**The change.** A canonicalization pattern on `reussir.record.dispatch`,
`MergeEquivalentDispatchRegions` (`lib/IR/ReussirOps.cpp`; the op gets
`hasCanonicalizer` in `include/Reussir/IR/ReussirOps.td`). Regions that do
not use their payload argument and hold the same operations (attributes and
locations included, on the same values from outside, values defined inside
corresponding by position) become one region over the union of their tags,
without the argument. Candidates are grouped by a structural hash first
(`regionHash`, which ignores locations and operand identity), and the
decision is the exact comparison (`sameOps`, through
`OperationEquivalence::isEquivalentTo`):

```c++
    for (unsigned i = 0; i < numRegions; ++i) {
      kept[i] = i;
      mlir::Region &region = op.getRegions()[i];
      if (!ignoresPayload(region) || boxesType(region, scrutineeType))
        continue;
      llvm::hash_code hash = regionHash(region);
      for (auto [otherHash, other] : candidates)
        if (otherHash == hash && sameOps(op.getRegions()[other], region)) {
          kept[i] = other;
          ...
```

A region that boxes a value of the scrutinee's own type (`boxesType`: a
token acceptor whose result is an rc of that type) keeps one copy per tag
(RV8C-03). The canonicalizer runs in the inliner and after the first SCCP,
before the decrement expansion, so each wildcard arm is expanded once.

**Why it is correct.** Running the same code for every merged tag is what
the copies did. The equality is exact and in region order, so the result is
deterministic, and the merged region's argument was unused, so dropping it
loses nothing. A wildcard arm can still depend on the tag at run time
(through a nested dispatch on the same scrutinee, or the scrutinee used
whole): the merged region re-reads the tag as the copies did. No pass
derives a fact from "region i holds tag i" except for single-tag regions:
destructuring decrement fusion and variant tag inference skip regions over
several tags, and ConvertToSTD lowers them through a pre-dispatch. The
release of the scrutinee in a merged region is then a plain decrement (its
drop dispatches on the tag, and its token is a dynamic one that token reuse
can still realloc). That costs exact-size reuse where a region rebuilds the
scrutinee's type, hence the boxing exception.

**Verification.**

- Tests: `tests/integration/conversion/record_dispatch_merge.mlir` (the
  merge, what is kept apart, and an executable check that the merged
  dispatch runs the right code for every tag) and
  `record_dispatch_merge_boxing.mlir` (regions boxing the dispatched type
  stay apart).
- The repro's times above.
- Smaller functions reach the inliner's size cap sooner: on lean2rr's
  StateT tower built without its inlining workaround
  ([issue 20](20-statet-tower.md)), rrc's peak memory went from 1.8 GB to
  2.4 GB with this patch alone; 0034 (issue 20) brings the series to 1.0 GB.
  With the workaround: unchanged.
- On the final stack (all 34 patches): Reussir's lit suite, 645 tests, 564
  passed, 81 unsupported, none failed; lean2rr's classic corpus builds and
  passes the oracle.

**Review.** Round 8, `reussir-c`
(local review notes, Q1): the equality is
sound (`OperationEquivalence::isEquivalentTo` with flags `None` compares
names, attributes, properties, result types, operands, locations, nested
regions and successors; probes kept apart ops with different attributes,
regions using different outside values, a nested use of the payload,
different op kinds and result types); no pass relies on a multi-tag region
holding one tag; a 6-variant program exercising wildcard releases,
construction in a merged arm, nested matches and the scrutinee used whole,
and issue 22's repro at N = 12, over six flag sets with an allocator shim:
identical output, as many frees as allocations, no size mismatch. One
finding, RV8C-03 (low, performance only): a merged arm that rebuilds the
scrutinee's type lost exact-size reuse (`_ => E::b{k, k, k}`: reuse
decisions {ensure 1, realloc 2, allocate 2} became {realloc 1}, 1500 more
allocator events per run). Resolved in the final patch: regions that box
the dispatched type are not merged. RV8C-02 (the rebase onto 0018-0027)
did not concern 0030, which applied cleanly.

**Effect on lean2rr.** Build time only: wildcard arms of lean2rr's output
(derived `BEq`/`DecidableEq` on wide inductives, and any `match` with a
default arm) are expanded once instead of once per covered constructor.
lean2rr's own workaround, `l2r_sink`, already bounded the cost of the
derived instances, and stays.

## Upstream note

The pattern compiler gives a match one region per variant, so a wildcard
arm is copied into every variant it covers, and the decrement expansion and
the first acquire/drop expansion expand each copy's releases in line: N^3
code for a derived equality over N constructors (N = 40: 444 s). Fix: a
canonicalization of `record.dispatch` that merges regions which ignore
their payload and hold identical operations into one multi-tag region,
except regions that box the dispatched type (they keep exact-size reuse).
