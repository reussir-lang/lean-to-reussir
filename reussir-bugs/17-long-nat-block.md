# 17. rrc memory is quadratic in the length of a straight-line function on `Nat`

## Summary

**Kind:** unclear. **Status:** worked around (build time only; lean2rr
cuts long functions into parts and turns `Array Nat` literals into
tables). No patch.

**Verdict: unclear.** The quadratic memory is real and also happens at
`-O none` (N = 250: 418 MB at `-O aggressive`, 160 MB at `-O none`;
N = 500: 1.18 GB, 401 MB, including about 12 s of texture build), so it is
neither the inliner nor `--reuse-across-call`. The pass responsible is not
found (the MLIR rrc prints for this program does not re-parse in
`reussir-opt`, which rejects an `rc<ffi_object>` member inside a value
record, so it could not be bisected by pass).

## Symptom and repro

Repro [`repros/bug17-long-nat-block.py`](repros/bug17-long-nat-block.py)
`N OUT.lean [Nat|UInt64]` writes

```
def longDo (x0 : Nat) : Nat → Nat
  | 0 => x0
  | k+1 => Id.run do
    let x1 := (x0 * 3 + x0) % 1000003
    ...                     -- N lets
    return longDo xN k
```

built through lean2rr with its workaround turned off (`L2R_NO_OUTLINE=1`).
It prints the same number as native Lean.

**Command.** `L2R_NO_OUTLINE=1 scripts/l2r.py` on the generated module.

**Expected.** rrc memory about linear in N.

**Actual on ef922049** (rrc only, this machine):

| N | `Nat` |
|---|---|
| 250 | 21 s, 417 MB |
| 500 | 32 s, 1.16 GB |
| 1000 | 57 s, 4.1 GB |

The same block on `UInt64` (`bug17-long-nat-block.py 1000 OUT.lean
UInt64`): 20 s, 127 MB. Sizes that hit the limits (before lean2rr's
workaround): 2500 `let`s ran out of memory (`std::bad_alloc` at 14 GB); a
test with a 1500-`let` function needed 5.5 GB. `--reuse-across-call` is
not the cause (1000 `let`s took 4.1 GB without it too).

## Cause

Not narrowed down. The memory is taken in rrc's MLIR lowering pipeline: a
build that stops after it (`--emit mlir-llvm`) already reaches the peak
(417 MB at N = 250, 1.19 GB at N = 500), while the IR it emits grows
linearly (301k and 565k lines). Probably a per-function analysis over
reference-counted values (`Nat` is a two-arm `[value]` enum whose `Big` arm
holds a box) keeps a set of live values per program point; with `UInt64`
there are no such values.

## lean2rr

As for [bug 16](16-nested-io-matches.md), a function with a tail path (or a
`let` value) of 256 `let`s is cut into parts of at most 64 `let`s on a
path, recursive functions included (`LeanToReussir/Outline.lean`). rrc on
the 1000-`let` block: 877 MB (was 4.1 GB; the rest grows linearly, about
0.3 MB per `Nat` operation); the repro's recursive function with 1000
`let`s: 37 s and 0.9 GB for the whole build, with 2500: 66 s and 2.1 GB
(was out of memory). A spliced `Array Nat` literal, one push per element,
becomes a table (plan §5.12): a 100000-element literal is one call.
`run.sh` builds the repro with `L2R_NO_OUTLINE=1`.
