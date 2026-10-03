# 16. Reuse across calls is superlinear in the nesting depth of matches

## Summary

**Kind:** cost (opt-in flag), with a small local fix. **Status:** patched
(0035), applied in `./reussir` (`l2r-local` cc8e5aa5); lean2rr also works
around it (it cuts deep tail paths and deep `let` values into functions),
and keeps doing so.

**Verdict: cost of the opt-in flag `--reuse-across-call`, not a defect.**
The flag is off by default, and its documentation says only that it may
increase peak heap use (`include/Reussir/Transformation/Passes.td`).
TokenReuse keeps tokens pending across non-tail calls and frees, at every
exit, each token not used there, so the exits deep in the nesting each
free many tokens. Counted on lean2rr's output (outlining off; calls whose
name starts with `__reussir_dealloc` in `--emit mlir-llvm`, that is
`__reussir_deallocate` and `__reussir_dealloc_unsized`, the two functions
`token.free` lowers to in `ReussirTokenFreeConversionPattern`): 1534 with
the flag and 325 without at N = 15, 5119 and 430 at N = 30. The excess,
1209 and 4689, is about 5·N² and grows 3.9x when the depth doubles. One
token per nesting level would give about N²/2, so each level seems to
leave several tokens pending, not one (an inference from these counts). The patch found why (below):
a token that a decrement's unique branch takes from an `scf.if` nested in
it was not collapsed into one free, so it was freed at every later exit.

With `--reuse-across-call`, the generated code grows quadratically with
match nesting depth (build time and memory). Each IO bind is a match on the
action's result whose ok arm holds the rest of the function, so a `main` of
N statements nests N matches deep.

## Symptom and repro

Repro [`repros/bug16-nested-io-matches.py`](repros/bug16-nested-io-matches.py)
`N OUT.lean` writes

```
def loop : Nat → IO Unit
  | 0 => pure ()
  | k+1 => do
    IO.println "line 0"
    ...                     -- N statements
    loop k
```

built through lean2rr with its workaround below turned off
(`L2R_NO_OUTLINE=1` in lean2rr's environment). It prints `line 0` to
`line N-1`.

**Command.** `L2R_NO_OUTLINE=1 scripts/l2r.py` on the generated module
(lean2rr's flags), and with `--no-reuse-across-call`.

**Expected.** Build time and memory about linear in N.

**Actual on ef922049** (rrc only, this machine; times from the quieter of
two runs, up to 2x longer on a busier host, memory the same):

| N | `--reuse-across-call` | without |
|---|---|---|
| 50 | 17 s, 261 MB | 14 s, 135 MB |
| 100 | 35 s, 1.15 GB | 15 s, 158 MB |
| 150 | 99 s, 3.1 GB (whole build) | |

Sizes that hit the limits (a `main` of N statements, before lean2rr's
workaround): 250 statements took about 200 s and 12.5 GB; 500 crashed rrc,
and the driver's retry without the flag took 434 s and 14.2 GB; 2000 was
killed after 1500 s. Without `--reuse-across-call`, 250 statements built in
16 s and 221 MB. The program is correct whenever the build finishes.

## Cause

TokenReuse's algorithm under `--reuse-across-call` (see the verdict: the
frees at every exit grow with the depth). `--reuse-across-call` lets
TokenReuse (`lib/Transformation/TokenReuse/TokenReuse.cpp`) keep tokens
alive across calls, and with it the code the lowering pipeline generates
grows quadratically with the nesting depth: the LLVM IR of the repro has
100k lines at N = 50 and 239k at N = 100 with the flag, 58k and 75k
without. The Reussir MLIR going into the pipeline is the same with and
without the flag.

## lean2rr

A function whose tail path is 32 matches (or `if`s) deep, or with a `let`
whose value is that deep, is cut: once a path is 8 levels deep, its rest
becomes a function called in tail position, and a deep value comes from a
function (`LeanToReussir/Outline.lean`, plan §10 "Build time"). In a
recursive function a rest that holds a tail call of the function's cycle
returns a step value instead (`done(v)`, or the callee and its arguments)
and the function makes the tail call itself, so its loops stay loops (a
1 MiB stack runs them: `tests/runtime/RtOutlineLoops`). rrc on 250
statements: 27 s, 343 MB; a 2000-statement `main`: about two minutes and
2 GB (before: killed after 1500 s); the repro's recursive loop with 500
statements: 23 s and 0.5 GB for the whole build, with 2000: 72 s and
1.5 GB. `run.sh` builds the repro with `L2R_NO_OUTLINE=1`, which turns the
cutting off.

## Patch

Patch file
[`patches/0035-l2r-local-bug-16-free-a-token-taken-from-a-nested-sc.patch`](patches/0035-l2r-local-bug-16-free-a-token-taken-from-a-nested-sc.patch)
(`l2r-local` commit `a639ae44`, applied in `./reussir`; `l2r-local` head
cc8e5aa5).

**What it fixes.** With `--reuse-across-call`, TokenReuse keeps every
available token across non-tail calls and frees a token that no allocation
reuses at every exit it reaches. A post-pass collapses those frees into
one free in the unique branch of the token's decrement, but only when that
branch yields the `nullable.create` of the reinterpreted box itself. When
the branch takes the token from an `scf.if` nested in it (the guard that
skips a tagged immediate under the special pointer tags, or a nested
decrement whose token `escapeTrappedTokens` brought out), the frees stayed
at the exits. lean2rr's IO code nests one match per statement, so the
error arm at depth d freed about every token made above it: quadratic
code. In the repro's `loop` at 50 statements: 15,650 free records for 49
reuses, up to 301 tokens carried across one call.

**The change** (`lib/Transformation/TokenReuse/TokenReuse.cpp`, the
post-pass that sinks frees): when the unique branch yields the result of
an `scf.if` in that branch with no other use, and the shared branch yields
a null, free that nullable once at the end of the unique branch:

```c++
+        auto elseNull = llvm::dyn_cast_if_present<ReussirNullableCreateOp>(
+            scfIf.getElseRegion().back().getTerminator()->getOperand(index)
+                .getDefiningOp());
+        auto nested =
+            llvm::dyn_cast_if_present<mlir::scf::IfOp>(yielded.getDefiningOp());
+        if (nested && nested->getBlock() == thenYield->getBlock() &&
+            yielded.hasOneUse() && elseNull && !elseNull.getPtr()) {
+          rewriter.setInsertionPoint(thenYield);
+          ReussirTokenFreeOp::create(rewriter, thenYield->getLoc(), yielded);
+          continue;
+        }
```

**Why it is correct.** A token reaches this post-pass only if nothing
reuses it on any path, so it is used by nothing but its frees, and the
original records free it once on every exit path. Freeing it once where it
is made, at the end of the unique branch, is equivalent: the free checks
for null, as the frees at the exits did, and the shared branch yields
null. The freed cell is dead and never reused, so moving its free earlier
reads nothing. A shape that does not match falls back to the frees at the
exits, as before.

**Verification.** Test `conversion/token_reuse_sink_escaped_free.mlir`;
`mutex_cell_drop.mlir` and `rwlock_cell_drop.mlir` now free the payload's
box before the cell's (both still after the unlock). On the repro through
lean2rr (`L2R_NO_OUTLINE=1`, rrc to the LLVM dialect): 50 statements,
13,401 deallocation calls -> 646 and 174 MB -> 123 MB; 100 statements,
51,601 -> 1,096 and 463 MB -> 127 MB. `run.sh` on the final stack:
`bug 16   FIXED       rrc: N = 50: 35 s, 159 MB; N = 100: 39 s, 190 MB
(1.18x memory); N = 100 without reuse across calls: 38 s, 183 MB`
(unpatched: 261 MB and 1.15 GB).

**Review.** Round RV8C (`~/Documents/l2r-scratch/rv8/reussir-c/FINDINGS.txt`,
Q6): no defect. The reviewer checked that a token is sunk only when its
decrement's token result has no other use, that later records of the same
token are skipped (no double free), that loops and calls keep their frees,
the changed order of a cell drop's two frees (both after the unlock), and
a program with nested matches and calls before and after over six flag
sets under an allocation-tracking shim (allocations equal frees).

**Effect on lean2rr.** Build time and memory without lean2rr's outlining.
lean2rr keeps its outlining (`Outline.lean`), which also bounds other
costs ([bug 17](17-long-nat-block.md)).

## Upstream note

With `--reuse-across-call`, a token that a decrement's unique branch takes
from a nested `scf.if` and that nothing reuses is freed at every later
exit (TokenReuse's sinking post-pass handles only a branch that yields the
`nullable.create` itself), so code grows quadratically with match nesting
(lean2rr's IO code: 50 nested matches, 15,650 free records for 49 reuses).
Fix: sink such a nullable's free to the end of the unique branch too.
