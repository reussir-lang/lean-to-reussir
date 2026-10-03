# 16. Reuse across calls is superlinear in the nesting depth of matches

## Summary

**Kind:** cost (opt-in flag). **Status:** worked around (build time only;
lean2rr cuts deep tail paths and deep `let` values into functions). No
patch.

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
leave several tokens pending, not one (an inference from these counts).

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
