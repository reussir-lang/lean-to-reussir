# 33. The decrement expansion crashes on an `rc.dec` without a token

**Kind:** bug (a crash on valid input), low severity. `reussir-opt`
only: rrc does not reach it. Two passes of Reussir read a result of
`reussir.rc.dec` that a valid operation need not have. Patch 33-a makes
the expansion leave such a decrement as it is.

## Summary

**Kind:** bug. **Status:** patched (33-a), patch 17 of the series on
upstream `36a55a0f` (Reussir branch `l2r-base13-r7`, tree `6dc99546`;
the patch is the file `patches/33-a-tokenless-rc-dec.patch`: 3 files,
+51/-0; 5 lines of code, 4 of pass description, a test of 42 lines).
It does not affect lean2rr: rrc's pipeline always runs the token pass
before the decrement expansion. `scripts/l2r.py` does not check for
the patch. The gate on the series with this form passed (gate 58,
2026-11-19).

**Upstream (2026-11-19):** Fixed upstream: pull request reussir#1095
is merged (commit `686c2f87`, 2026-11-19), with this entry's patch.
The patch stays in the series until lean2rr's base moves past that
commit; then this entry, its patch and its repro are deleted (README
policy). At `36a55a0f` the bug is open (confirmed on pristine
upstream). The two pull requests:

- reussir#1093, the first form of 33-a (the expansion made the missing
  token itself): closed by the maintainer on 2026-11-19, rejected. The
  reason: the token pass runs before this pass by design, so the pass
  must not do that pass's work; it must only not crash, that is, test
  and leave an operation that it cannot expand.
- reussir#1095, the form of this entry: merged on 2026-11-19 as
  `686c2f87`.

Found during the work on patch 31-a
([entry 31](31-leaf-foreign-release.md)). The patch applies to a clean
`36a55a0f` alone.

## Context

- **`reussir.rc.dec`** releases a counted box. It can have a result, a
  *token*: the freed memory, which a later allocation can use again.
- **The producer phase** of the pass `reussir-token-instantiation`
  gives each decrement of a shared box its token result.
- **The decrement expansion** (`reussir-rc-decrement-expansion`, and
  `reussir-acquire-drop-expansion` with `expand-decrement`) writes each
  decrement out as "the count is 1: release the contents and keep the
  token; else decrement the count".
- A decrement without a token is valid: the verifier accepts it for a
  shared box (`lib/IR/ReussirOps.cpp:728`), the frontend emits it,
  `rrc --emit mlir` prints it, and two upstream passes that run before
  the producer phase create it. By upstream's design the producer
  phase must run before the expansion.

## Symptom and repro

Repro [`repros/bug33-tokenless-rc-dec.mlir`](repros/bug33-tokenless-rc-dec.mlir):
one function with a `reussir.rc.dec` of a shared box of a record of
scalars, with no token result.

**Command.** `reussir-opt bug33-tokenless-rc-dec.mlir
--reussir-rc-decrement-expansion` (the same with
`--reussir-acquire-drop-expansion='outline-record=true
expand-decrement=true'`).

**Expected:** no crash.

**Actual on pristine `36a55a0f`:** exit 139 (SIGSEGV in the rewrite
pattern). With the token pass first: exit 0, the decrement expanded.

**With 33-a:** exit 0, and the `rc.dec` is printed unchanged. With
`--reussir-token-instantiation` first, the decrement is expanded as
before.

`run.sh`'s `bug33` in the gate on the series of 18 patches (gate 58):
REPRODUCES on pristine `36a55a0f` (`reussir-opt` crashes), FIXED on
the series (the decrement is left unexpanded, with no crash).

## Cause

`RcDecrementExpansionPattern`
(`lib/Conversion/RcDecrementExpansion/RcDecrementExpansion.cpp:159` at
`36a55a0f`) reads the type of the token result with
`llvm::cast<NullableType>(op.getNullableToken().getType())`. A
decrement without a token has no such result, so this is a read through
a null value. The pass has a precondition that it does not check: the
producer phase must have run.

## lean2rr

Not reached. rrc's pipeline (`crates/reussir-backend/src/pipeline.rs`)
runs the producer phase before both expansions at every level. It
matters only for someone who runs `reussir-opt` on frontend MLIR by
hand, as a lit-style test does.

One effect inside the series, with patch 31-a
([entry 31](31-leaf-foreign-release.md)): before 31-a, the body of a
foreign release function sat in worklist glue, where a missing token is
handled. With 31-a the body of a leaf record's release stays in the
function. A `reussir-opt` pipeline run by hand without the token pass
then reached the crash on such an input, where pristine upstream
expands it. With 33-a that run exits 0 and **leaves the decrement
unexpanded**: such a pipeline no longer expands that input. With the
token pass first it expands as before. This is the behaviour that the
maintainer asked for (run the token pass first).

## Patch

[`patches/33-a-tokenless-rc-dec.patch`](patches/33-a-tokenless-rc-dec.patch),
`[rc] leave a decrement without a token result unexpanded`.

In the pattern, after the exit for rigid boxes, foreign objects and
closures and before any read of the token:

```cpp
    if (!op.getNullableToken())
      return rewriter.notifyMatchFailure(op, "requires token instantiation");
```

The description of `reussir-rc-decrement-expansion` (`Passes.td`) now
says that the producer phase must run first and that a decrement
without its token result is left unexpanded.

**The precedent.** Upstream's pattern for `array.create`
(`lib/Conversion/ConvertToSTD/ConvertToSTD.cpp`) does the same, word
for word, when its token is missing: a match failure, the pass
succeeds, the operation stays.

**What happens after it.**

| Pass on a decrement without a token | Result |
|---|---|
| `--reussir-rc-decrement-expansion` | exit 0, the `rc.dec` unchanged |
| `--reussir-acquire-drop-expansion` with `expand-decrement`, an ordinary function | exit 0, unchanged |
| the same, inside worklist glue (upstream's foreign release function) | as before the patch: another pattern handles a missing token itself |
| then `--reussir-convert-to-llvm` | exit 1 with MLIR's generic message `failed to legalize operation 'reussir.rc.dec' that was explicitly marked illegal`, at the operation's location |

So the error that a user sees comes from the conversion to LLVM and
does not name token instantiation. A named error there is a possible
follow-up; it is not in the patch.

**The other reads of the token.** Every other place in Reussir's
passes that reads a decrement's token tests it first (read, seven
places); nothing else needs a guard.

**Tests.** `conversion/rc_dec_expansion_missing_token.mlir`: two
functions (a leaf record, a pinned variant), three RUN lines: both
passes without tokens (the `rc.dec` must be the function's only
operation before the return), and the token pass first (expanded, no
`rc.dec` left). On pristine upstream the first two RUN lines crash;
with the patch all three pass, also on the series.

## Review

- **The first form** (make the token; reussir#1093) was reviewed
  independently and accepted (local notes `port13/reviews/RV1`, the
  section on 33-a). It is not in the series any more. Its key argument
  holds for this form too: between the new exit and the old read of
  the token's type every path reaches the read, so every decrement
  that takes the exit crashed before. A program that compiled before
  can therefore not take it.
- **This form** follows the maintainer's direction on reussir#1093.
  It is reviewed independently and accepted (the same notes, the
  section on the reworked 33-a): "It does what the maintainer asked
  and nothing else." Checks of the reviewer:
  - The guard is before the first operation that the pattern creates,
    so the pattern changes nothing before it reports the failure; the
    three reads of the token in the pattern are after it.
  - The pass cannot fail on the operation that stays: both passes
    rewrite greedily, with no legality check. Run: 65 runs over 5
    inputs without tokens and every option set that upstream's tests
    use; pristine crashes in 37 of them, the patched tool exits 0 in
    all 65.
  - The form with a token is unchanged: 24 inputs with 11 option
    sets, the token pass first: 264 of 264 outputs and exit codes
    equal to pristine.
  - Objects of two lean2rr programs on the series of 18 against the
    series of 17: byte-identical.
- The reviewer's unverified note about an MLIR assertion in upstream's
  `replaceWithProduced` was about the first form's call of that
  function. This form does not call it. The note stays what it was: a
  doubt about upstream's own producer phase, from memory, not verified
  (no MLIR build with assertions on was run).
- Formatting: the patch's changed lines are clean under clang-format
  23.1.0 (LLVM style).

## Measured claim

The claim is "no generated code changes", and by the argument above it
holds for every program that compiled before. Measured for this form:

| Set | Result |
|---|---|
| lowered MLIR of five upstream units (core, std, mltt, rbtree, nbe-hoas), pristine rrc against pristine with 33-a, `-O aggressive --reuse-across-call` | 5 of 5 byte-identical |
| objects of 8 lean2rr programs, the series of 17 patches against the series of 18 (which also has 35-a and the formatting changes) | 8 of 8 byte-identical |
| Reussir's tests, pristine with 33-a: lit, the subset for decrements, tokens and expansion; unit tests | 47 pass, 1 fails for a reason of the build machine (a tool that is not built), the same on pristine; 97 of 97 |
| the series with this form (before 35-a and the formatting changes): 6 lit tests; 6 runtime tests of lean2rr | 6 of 6; 6 of 6 |

The measurements of the first form (33 upstream units, 40 lean2rr
objects, the gates on 16 and 17 patches) are in git history; they are
not claims about this form.

No timing was made: rrc never takes the new exit.

**The gate** (gate 58, the series of 18 patches against the gate on
17): all 742 `.rr` files byte-identical; all 742 executables have the
same sizes of every section; in the 106 that were sampled `.text`,
`.data`, `.data.rel.ro` and `.eh_frame` are byte-identical.

**Not measured:** the 33 upstream units with this form.

## Upstream note

Pull request reussir#1095 is merged (2026-11-19, commit `686c2f87`).
reussir#1093 (the first form) is closed.
