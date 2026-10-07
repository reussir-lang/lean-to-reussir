# Testing and correctness

<p class="lead">How lean2rr checks that a translated program behaves like the
native build. Sources: the <a href="repo:tests/README.md">tests README</a>
and translation plan §8.</p>

## The oracle is the native build

<div class="rule" markdown="1">
Every test builds the same Lean program twice: natively, with stock Lean
{{v:lean}}, and through lean2rr. Both executables run with the same
arguments and input. The test passes when standard output, standard error
and the exit code are equal, byte for byte.
</div>

Panic backtraces are turned off on both sides (`LEAN_BACKTRACE=0`), because
they contain addresses. The differences listed in plan §10 are the only
accepted ones.

**Expectation files.** Some tests show an intended difference of plan §10:
a Lean runtime bug that lean2rr does not reproduce, or a trace that prints
twice (`RtCseApart`). Such a test pins both outputs of each stream
that differs: `NAME.native.out` (or `.err`, `.code`) for the native run,
and `NAME.l2r.out` (or `.err`, `.code`) for the lean2rr run. Each run is
compared with its own file, so the test fails if either output changes.
A `NAME.refused` file expects lean2rr to refuse the program at
translation, with the lines of the file in its message.

{{svg:runsh}}

## The test sets

{{gen:testsets}}

Tests marked `.xfail` (known to fail; the file says why):

{{gen:xfail}}

### The classic corpus

The reference for correctness and performance. Every program has a size
argument and prints a few checksum lines that depend on all the work.
`tests/oracle.py` builds the native programs, records their outputs, checks
an alternative build against them, and times both.

{{gen:classic}}

### The last full run

The gate of switch step 10 (branch `lean-runtime-step10` at 0410be6), against
native Lean 4.34.0, 2026-10-06:

- runtime suite: 336 of 337 identical to native, some of them through
  expectation files; the other one is the expected failure
  `RtLeanUnsupported`;
- loader checks: 17 of 17;
- classic corpus: 54 of 54, with all optional passes on and with all off;
- Reussir benchmark suite: 18 of 18;
- `leanrt` unit tests 46 of 46; lean-runtime's rows all agree; the
  inline, constant-read, conversion-count and big-number checks pass.

No correctness failure. Each switch step passed such a gate before its
merge.

## Review rounds

Reviewers try to break lean2rr. A reviewer reads the code, forms a
hypothesis, and confirms it with a small program. There is no brute-force
fuzzing and no huge input: inspection with targeted programs finds more.

| Rounds | Finding ids (examples) |
|---|---|
| 1 to 5 | `RP3-1`, `PF4-07`, `ST4-10` |
| 6 | `RV6…`, `IO6…`, `TY6…`, `PRG6…` |
| 7 | `RV7…` |
| 8 | `RV8…` |
| 9 | `RV9…`, and the reviews of its fixes `C01R…` to `C03R…` |
| after round 9: the review of each change | `REB…` (the extern rule), `RSG…` (library initializers), `CLR…` (`conv-liveness`), `RULR…`, `RST2…`, `RST3…`, `RS4…` to `RS7…` (the switch steps) |

{{svg:review}}

- **Judge first.** A judge decides whether a finding is real before anyone
  fixes it: a lean2rr bug, a documented difference, or no defect.
- **Every repro becomes a test.** Each consistently reproducible lean2rr bug
  gets a regression test in `tests/runtime` in the same commit as its fix. A
  bug that is not fixed yet gets a test with `.xfail`.
- **Every fix is reviewed.** A reviewer tries to break the fix. After a
  rework, the fix is reviewed again.
- The [tests README](repo:tests/README.md) maps each finding to its test.

## Other evidence

### Lean's own compiler tests

Review round 9 ran the test programs of Lean's own repository
(`tests/compile` and `tests/compile_bench`, Lean 4.33.0) through lean2rr: 72
programs in scope, 2 adapted programs and 9 programs derived from them. All
gave the same output and exit code as native.

### Tests derived from Crane

Crane is Bloomberg's Rocq-to-C++ extractor, another typed code generator
with reference counting. Review round 9 re-expressed shapes from Crane's
regression tests in Lean. They found no bug, and nine of them became
runtime tests (`RtGrammarActions`, `RtComputedFnTypes`, `RtSharedOnOnePath`,
`RtDropMediated`, `RtConvMediated`, `RtReuseAlias`, `RtUniformFnTypes`,
`RtMutualTailArgs`, `RtTaskCaptureUpdate`).

### Tests derived from CSLib

CSLib is a library of computer science in Lean. It imports Mathlib, and
lean2rr does not support Mathlib (translation plan §10). Review round 9
copied the computational code of CSLib into programs that import only
`Init`, without the proofs: a cost-counting monad, insertion sort and merge
sort in any monad, Turing machines, register machines and CCS processes.
All programs gave the same output as native, and five of them became
runtime tests (`RtCslInsertion`, `RtCslMergeSort`, `RtCslTuring`,
`RtCslURM`, `RtCslVending`). Each test keeps the copyright notices of the
CSLib and Mathlib files that it copies.

## Checking the rules

Plan §8 lists the points reviewers check against Lean's compiler sources,
`lean.h`, or a small native experiment: Stage 1 against Lean's specializer,
dictionary folding, that Stage 3 never guesses a type, arity and closure
timing, the join-point strategies, extern semantics, startup order, and that
nothing lets Reussir or LLVM drop or reorder effects.
