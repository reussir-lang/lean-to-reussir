# 33. The decrement expansion crashes on an `rc.dec` without a token

**Kind:** bug (a crash on valid input), low severity. `reussir-opt`
only: rrc does not reach it. No patch.

## Summary

**Kind:** bug. **Status:** not patched. It does not affect lean2rr:
rrc's pipeline always runs the token pass before the decrement
expansion, so the expansion never sees the input that crashes it.

**Upstream (2026-11-18):** Open at `36a55a0f` (confirmed on pristine
upstream). Not reported. Found during the work on patch 31-a
([entry 31](31-leaf-foreign-release.md)).

## Symptom and repro

MLIR written by hand (or the output of `rrc --emit mlir`, which prints
this form): an ordinary function with a `reussir.rc.dec` of a shared
box that has no token result.

**Command.** `reussir-opt FILE
--reussir-acquire-drop-expansion='outline-record=true expand-decrement=true'`

**Expected:** a diagnostic, or the pattern does not apply.

**Actual on pristine `36a55a0f`:** SIGSEGV inside a rewrite pattern.
With `--reussir-token-instantiation` first, the same input passes.

The repro is not in [`repros/`](repros/) (it is in the local notes of
the port, `port13/i5/l31/q_leaf.mlir`).

## Cause

The input is valid: the verifier of `rc.dec` accepts a missing token on
a shared box (`lib/IR/ReussirOps.cpp:727`), and this is the form that
the frontend emits before the pass `reussir-token-instantiation`.
`RcDecrementExpansionPattern` then casts the type of the token result
(`llvm::cast<NullableType>(op.getNullableToken().getType())`), and the
result does not exist. So the pass has a precondition that it does not
check: it must run after the token pass. The bug is in the pass, not in
the verifier.

## lean2rr

Not reached. rrc's pipeline (`crates/reussir-backend/src/pipeline.rs`)
runs the token pass before the expansion at every level. It matters
only for someone who runs `reussir-opt` on frontend MLIR by hand, as a
lit-style test does.

One effect on the series: before patch 31-a, the body of a foreign
release function sat in worklist glue, where a missing token is
accepted. With 31-a the body of a leaf record's release stays in the
function, so such an input now reaches this crash where pristine
upstream accepts it. The tests of the series use the token form, as
upstream's own tests do.

## Patch

None. A fix would be small (return a failure from the pattern, or emit
a diagnostic, when the token result is missing), but lean2rr does not
reach the bug, and nobody wrote or reviewed one.

## Upstream note

Not reported. A report would give the one function and the one
command.
