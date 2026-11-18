# 33. The decrement expansion crashes on an `rc.dec` without a token

**Kind:** bug (a crash on valid input), low severity. `reussir-opt`
only: rrc does not reach it. Two passes of Reussir read a result of
`reussir.rc.dec` that a valid operation need not have. Patch 33-a lets
the expansion make that result itself.

## Summary

**Kind:** bug. **Status:** patched (33-a), patch 15 of the series on
upstream `36a55a0f` (Reussir branch `l2r-base13-r4`, commit `bf8f8de0`;
3 files, +77/-0; 10 of the lines are code and pass description, the
rest is the test). It does not affect lean2rr: rrc's pipeline always
runs the token pass before the decrement expansion. `scripts/l2r.py`
does not check for the patch.

**Upstream (2026-11-18):** Open at `36a55a0f` (confirmed on pristine
upstream). Not reported: the maintainer takes fixes from this
directory. Found during the work on patch 31-a
([entry 31](31-leaf-foreign-release.md)). The patch applies to a clean
`36a55a0f` alone.

## Context

- **`reussir.rc.dec`** releases a counted box. It can have a result, a
  *token*: the freed memory, which a later allocation can use again.
- **The producer phase** of the pass `reussir-token-instantiation`
  gives each decrement of a shared box its token result (the rewrite
  `replaceWithProduced`).
- **The decrement expansion** (`reussir-rc-decrement-expansion`, and
  `reussir-acquire-drop-expansion` with `expand-decrement`) writes each
  decrement out as "the count is 1: release the contents and keep the
  token; else decrement the count".
- A decrement without a token is valid: the verifier accepts it for a
  shared box (`lib/IR/ReussirOps.cpp:728`), the frontend emits it,
  `rrc --emit mlir` prints it, and two upstream passes that run before
  the producer phase create it.

## Symptom and repro

Repro [`repros/bug33-tokenless-rc-dec.mlir`](repros/bug33-tokenless-rc-dec.mlir):
one function with a `reussir.rc.dec` of a shared box of a record of
scalars, with no token result.

**Command.** `reussir-opt bug33-tokenless-rc-dec.mlir
--reussir-rc-decrement-expansion` (the same with
`--reussir-acquire-drop-expansion='outline-record=true
expand-decrement=true'`).

**Expected:** the expanded decrement, as when
`--reussir-token-instantiation` runs first.

**Actual on pristine `36a55a0f`:** exit 139 (SIGSEGV in the rewrite
pattern). With the token pass first: exit 0. With 33-a: exit 0, and
the output has the expanded decrement.

Runs: the patch's author and its reviewer (pristine 139, patched 0);
the gate on the series by hand (pristine exit 139, the series exit 0,
23 lines of MLIR); and `run.sh`'s function `bug33`, in a run of the
function's author: REPRODUCES on pristine, FIXED on the series. The
gate did not run `bug33` through `run.sh`.

## Cause

`RcDecrementExpansionPattern`
(`lib/Conversion/RcDecrementExpansion/RcDecrementExpansion.cpp:159` at
`36a55a0f`) reads the type of the token result with
`llvm::cast<NullableType>(op.getNullableToken().getType())`. A
decrement without a token has no such result, so this is a read through
a null value. The pass has a precondition that it does not check: the
producer phase must have run. The bug is in the pass, not in the
verifier.

## lean2rr

Not reached. rrc's pipeline (`crates/reussir-backend/src/pipeline.rs`)
runs the producer phase before both expansions at every level. It
matters only for someone who runs `reussir-opt` on frontend MLIR by
hand, as a lit-style test does.

One effect inside the series: before patch 31-a, the body of a foreign
release function sat in worklist glue, where a missing token is
accepted. With 31-a the body of a leaf record's release stays in the
function, so such an input reached this crash where pristine upstream
accepted it. With 33-a it is expanded.

## Patch

[`patches/33-a-tokenless-rc-dec.patch`](patches/33-a-tokenless-rc-dec.patch),
`[rc] expand a decrement that has no token result`.

In the pattern, after the test that leaves rigid boxes, foreign objects
and closures alone:

```cpp
    if (!op.getNullableToken())
      return op.replaceWithProduced(rewriter);
```

`replaceWithProduced` is the rewrite that the producer phase applies.
The greedy driver then visits the rebuilt decrement, and the unchanged
code expands it. One change covers both passes (they share the
pattern).

Why this and not a diagnostic: the input is valid at this stage, and a
fix must work in pipelines other than rrc's. Why the token is right:
the expansion is the last user of the attributes that decide a token's
type, so the type is final there. Which decrements can take the new
branch: only shared boxes that are not foreign objects or closures,
which is exactly the set that the producer phase gives a token; so the
rebuilt operation always verifies.

**Tests.** `conversion/rc_dec_expansion_missing_token.mlir`: four
functions (a leaf record, a variant that is not pinned, a pinned one,
a foreign release function in the form that `rrc --emit mlir` prints),
through both passes. On pristine upstream `reussir-opt` crashes on both
RUN lines; with the patch both pass.

## Review

Accepted by an independent reviewer (local notes
`port13/reviews/RV1`, the section on 33-a).

- **The key argument.** Between the new test and the old read of the
  token's type there is no return. So before the patch, every decrement
  that now takes the new branch crashed. A program that compiled before
  can therefore not take it: the patch can only change inputs that
  crashed.
- **Output.** For the test file, and for the reviewer's own probes
  (boxes of every capability, a worklist variant with a foreign member
  through one and two passes, both drop orders), the patched pass gives
  byte for byte the output of pristine upstream with the token pass
  first.
- **What stays as it was.** Foreign objects (also tagged ones) and
  rigid boxes are untouched. A decrement inside worklist glue gets no
  token: another pattern takes it first and frees the box in place, as
  on pristine.
- Findings, low: the test's second RUN line has no positive check for
  two of the four functions; no negative case for a decrement in
  worklist glue.
- **An unverified note of the reviewer, not a finding of a bug:**
  upstream's `replaceWithProduced` replaces an operation with no result
  by one with one result through `replaceOp`; MLIR is said to assert
  equal result counts there. The reviewer wrote this from memory of
  MLIR's source and could not run it (the installed MLIR has assertions
  off); the patch's author has the same doubt. If it holds, it holds
  for upstream's own producer phase on every decrement of every
  program, with or without 33-a. It is not verified, so it is recorded
  here as a note only.
- Not checked: clang-format (not installed on the build machine); a
  build of MLIR with assertions on.

## Measured claim

The claim is "no generated code changes", and by the key argument
above it holds for every program that compiled before. Measured:

| Set | Result |
|---|---|
| upstream's benchmark suite (31 programs), core and std, pristine against pristine with 33-a, `-O aggressive --reuse-across-call`, lowered MLIR | 33 of 33 units byte-identical |
| objects of lean2rr programs, the series of 15 patches against the series with 33-a | 40 of 40 identical |
| the gate on the series of 16 patches against the gate on 15: all 742 executables of the runtime suite | section sizes identical in all 742; `.text` and `.data` byte-identical in the 106 that were sampled |
| Reussir's tests on the series of 16: selected lit tests, `reussir-ut`, cargo tests | 247 pass and 0 fail of 267 selected (20 unsupported on the build machine); 97 of 97; 0 failed |

No timing was made: rrc never takes the new branch, and on its normal
path the pattern gains one test of a result for null.

**Not measured:** an MLIR build with assertions on.

## Upstream note

Not reported. A report would give the one function, the one command
and the two lines of the fix.
