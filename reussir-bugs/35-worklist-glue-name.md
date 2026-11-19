# 35. The worklist glue computes a glue function's name at every request

**Kind:** cost (build time). Not a bug: the generated code is correct.
Each time a drop asks for a worklist glue function, Reussir prints the
glue's whole signature and hashes the text to get the function's name,
also when the function exists already. In a program with long, nested
types this takes most of one pass. Patch 35-a keeps the function for
each signature and role during one run of the pass. It is an
optimization.

## Summary

**Kind:** cost. **Status:** patched (35-a), patch 13 of the series on
upstream `36a55a0f` (Reussir branch `l2r-base13-r7`, tree `6dc99546`;
the patch is the file `patches/35-a-worklist-glue-name-cache.patch`: 4
files, +56/-45, no test). `scripts/l2r.py` does not check for the
patch: without it the programs are the same and one kind of program
builds more slowly. The gate on the series with it passed (gate 58,
2026-11-19).

**Upstream (2026-11-19):** Open at `36a55a0f`: the code is from
upstream's drop series of 2026-11-01. Not reported. The form in the
series applies after 34-a; a form for a clean `36a55a0f` exists (the
same change with other context lines).

## Context

- **Worklist glue.** Upstream's drops release a value's dead children
  through *glue functions*, one for each dropped type, role (drop,
  release, decrement, array drop) and direction.
- **The name.** A glue function's symbol name is
  `REUSSIR_DROP_<role>_<direction>` plus a hash of the printed function
  type. The glue is made once for each name: a request looks the name
  up in the module's symbol table and makes the function only when it
  is not there.
- **`ReussirAcquireDropExpansionPass`** is the module pass that makes
  these requests, once for each drop site and again while it builds
  each glue body.

## Symptom

`RtDepPolyRec`, a runtime test with polymorphic recursion (a 6 MB
`.rr`, 3794 functions, 218 types), the same `.rr` on both bases, one
run each:

| Phase (wall seconds) | `l2r-base12` | the series of 16 patches |
|---|---:|---:|
| MLIR lowering pipeline | 64.9 | 83.0 |
| of it `ReussirAcquireDropExpansionPass` (its two runs) | 6.95 (2.2 + 4.7) | 35.6 (1.2 + 34.5) |
| translation to LLVM IR | 2.8 | 1.7 |
| LLVM optimization | 26.3 | 15.2 |
| LLVM code generation | 23.2 | 11.3 |
| total to the executable | 119.8 | 113.2 |

**The build time of this test is not a regression** of the port: the
total is lower on the new base, because the module is about half the
size and LLVM's phases are faster. (The gates on the old base had
122 s to 145 s for it. An earlier note compared its 136 s with 671 s,
which was the wall time of the old suite in 8 parallel shards.) But
one pass is seven times slower, and that is the cost of this entry.

Stack samples in that pass (7 samples): 6 are in the printers of
record and closure types under MLIR's type printer; the two whose
caller is visible come from `WorklistGlue::function`.

## Cause

`WorklistGlue::function`
(`lib/Conversion/AcquireDropExpansion/WorklistDrop.cpp:51-71` at
`36a55a0f`) prints the glue's signature with the bodies of its records
and hashes the text **at every call**, before it looks the name up. So
the cost is the number of requests times the length of the printed
signature. In a program of polymorphic recursion the signatures are
long (records nested through pairs, lists and closures), and each drop
site of each glue body asks again. The glue itself was already made
once; only its name was computed for each use.

The lines are identical in pristine upstream; the local patches 10-a,
31-a and 32-a touch the file but not this code.

## lean2rr

lean2rr reaches it in every build, but it is measurable only for one
class of program: long signatures that are requested very often. Of
seven programs measured, one shows it (`RtDepPolyRec`). The translator
has no reasonable change to make: nothing in the shape of its output
is at fault.

## Patch

[`patches/35-a-worklist-glue-name-cache.patch`](patches/35-a-worklist-glue-name-cache.patch),
`[drop] look worklist glue up by signature before naming it`.

- **Owner and lifetime.** The pass already makes one collection of
  symbol tables for each run and hands it to its patterns and helpers.
  A new struct `DropGlueSymbols` holds that collection and a map; the
  pass's local variable is of this type. The map dies with the run.
  There is no static state.
- **Key.** (module, function type, role attribute). All three are
  uniqued handles of the IR. The function type holds the dropped type
  and the `indexed` argument; the attribute holds the role and the
  direction. These are exactly the inputs of the name, so one key has
  one name.
- **Value.** The function itself. A hit does no printing, no hashing
  and no lookup in the symbol table. A miss computes the name and
  looks it up as before (the glue can exist from an earlier run of the
  pass or from the input) and then records the function. A new
  function is recorded directly after it enters the symbol table,
  before its body is built, so the requests that the body makes find
  it.
- **Without a collection** (the public default of the helpers) one
  request gets a local struct: the function is resolved by name each
  time, as before.
- **Threads.** The pass is a module pass, and its greedy rewrite of the
  module is sequential. The map is a local of one run, so nothing is
  shared between threads or runs.
- **Validity.** The same condition that the symbol tables already
  need: the pass does not erase or rename functions.

**Composition, not inheritance.** The first form derived the struct
from MLIR's `SymbolTableCollection`. The review asked for a struct that
holds the collection (finding C1), and the patch has this form: the
helpers that take plain tables get `&symbols->tables`.

**A changed public signature.**
`populateAcquireDropExpansionConversionPatterns` (a public header) now
takes `DropGlueSymbols *`. Its only caller in the tree is the pass. A
caller outside the tree that passes a `SymbolTableCollection *` must
change (finding C2).

**Tests.** None added: names and IR do not change, so the only thing
to observe is build time. The evidence is identity (below).

## Review

Accepted by an independent reviewer (local notes `port13/reviews/RV1`,
the section on 35-a): "I found no way to make the cache return a
function that the name lookup would not return." That review was of
the first form (inheritance). The form in the series (composition,
finding C1) was reviewed again by the same reviewer and accepted:
"Only the carrier changed." Every use site was checked, the null case
is kept at each, and 76 of 76 outputs and exit codes of `reussir-opt`
are equal to pristine (19 inputs, two drop orders, one run and two
runs of the pass). The timing was not repeated in the second review.

- **Stale entries.** None possible: every erase or replace in the
  pass's directory (about 40 sites) acts on an operation inside a
  function, never on a function; the pass has no step that removes
  functions. The symbol tables next to the map would dangle in the
  same cases.
- **Key.** Complete: what is not in the name is not in the key either,
  and upstream already shares one function for each name across those
  things. Two drop orders in one run need nested modules; a module
  with two nested modules, backward and forward, gives output
  byte-equal to pristine.
- **Glue that exists before the run.** 18 lit inputs, two drop orders,
  one run and two runs of the pass: 72 of 72 outputs and exit codes
  equal to pristine `reussir-opt`.
- **Identity, the reviewer's own builds.** Lowered MLIR of 5 upstream
  units byte-identical; objects of 4 lean2rr programs byte-identical.
- **Time, the reviewer's own single run** (`RtDepPolyRec`, to the
  object file): the pass 35.3 s to 4.9 s, the MLIR pipeline 85.5 s to
  55.0 s. The numbers to the executable are the author's only.
- Findings, all low: C1 (done), C2 (above), C3 (the module in the key
  is redundant for rrc and costs nothing).
- Not checked by the reviewer: executables, the full lit suite. From
  the reviewer's knowledge of MLIR and not read again: that the greedy
  driver does not erase a function.

## Measured claim

**Build time** (the driver's exact rrc command with only the rrc binary
changed, the two sides in turn; the series of 17 patches against the
same with 35-a; one warm texture store on a memory file system; 3 runs
to the executable for each side, median (min); a shared machine, load
3 to 8):

| `RtDepPolyRec` (6 MB of `.rr`) | before | with 35-a |
|---|---:|---:|
| `ReussirAcquireDropExpansionPass`, its two runs | 35.83 s (35.12) | 5.11 s (5.03) |
| MLIR lowering pipeline | 83.58 s (83.09) | 53.89 s (53.67) |
| source to executable | 116.66 s (112.47) | 84.37 s (83.64) |
| CPU time of the process tree, median | 168.0 s | 135.7 s |

The object file and the executable are byte-identical in each pair.

**Other programs** (the same method):

| Program (size of the `.rr`) | pass, before | pass, with 35-a | total, before | total, with 35-a |
|---|---:|---:|---:|---:|
| `RtTArrKinds` (2.7 MB) | 0.720 s | 0.786 s | 34.88 s | 35.48 s |
| `RtCArrKinds` (2.4 MB) | 0.671 s | 0.581 s | 28.95 s | 28.25 s |
| `RtDepPayloadObjects` (1.6 MB) | 0.478 s | 0.476 s | 16.23 s | 16.74 s |
| `RtOutlineStates` (0.6 MB) | 0.061 s | 0.058 s | 8.05 s | 8.62 s |
| `RtNat` (0.3 MB) | 0.057 s | 0.052 s | 2.90 s | 2.76 s |
| the classic `rbmap` (0.1 MB) | 0.021 s | 0.020 s | 1.20 s | 1.20 s |

Objects and executables are identical for all six. No program other
than `RtDepPolyRec` gains or loses measurably: the minima agree within
0.2 s (total) and 0.05 s (pass), and the medians move both ways. So
35-a removes the cost of **one outlier class** (long signatures that
are requested very often). It is not a broad gain.

**Upstream's units** (pristine `36a55a0f` against pristine with 35-a;
core, std and 31 benchmark programs, lowered MLIR): 33 of 33
byte-identical, for the first form and again for the form in the
series. Pass time on the two largest units: no measurable change (std
267 ms to 227 ms, mltt 131 ms to 145 ms, medians of 3).

**The form in the series** (composition, on the series of 18): objects
of 8 lean2rr programs byte-identical to the series of 17
(`RtDepPolyRec` among them); `RtDepPolyRec`'s pass in one run: 4.83 s.
The changed lines are clean under clang-format 23.1.0.

**Reussir's tests** (pristine with 35-a): the lit subset for drops,
foreign code and integers gives the same result as pristine on each of
its 131 tests (115 pass, 15 unsupported, 1 failure of the build
machine); 97 of 97 unit tests.

**Through lean2rr:** 8 runtime tests pass on the series of 17 with
35-a (`RtDepPolyRec`, `RtTArrKinds`, `RtHashMap` and five tests of
release order and integers). The gate on the series of 18 patches (gate 58, lean2rr dev `6fb19b4e`,
2026-11-19) passed: 748 of 750 runtime tests with 2 expected failures,
23 of 23 check scripts, the classic corpus in its three modes, the
raytracer, the repros. Generated code is that of the
gate on 17 patches: all 742 executables have the same sizes of every
section, and the 106 that were sampled are byte-identical in `.text`,
`.data`, `.data.rel.ro` and `.eh_frame`. In the gate `RtDepPolyRec`
takes 105.4 s in rrc and the link (137.2 s in the gate before; one
run, with 8 shards at once). The sum of rrc and the link over the
other 741 tests is 2722 s against 2715 s: at the level of the suite,
35-a's gain is that one program. The suite's wall time does not move
(601 s against 603 s), because the program is not in the longest
shard.

**Not measured:** the number of glue requests and the lengths of the
signatures; whether the cost grows faster than the module (no
half-size variant was built); the 3.9 s that the pass's second run
still takes on `RtDepPolyRec` (not profiled; `l2r-base12` took 4.7 s
for the same phase); the full lit suite, clang-tidy and the sanitizer
tests.

Also seen in `RtDepPolyRec`'s build and not looked at further:
upstream's pipeline has one more SCCP pair after token reuse than on
`l2r-base12` (about 8 s there).

**Repro.** None in `run.sh`: the entry has nothing to observe but
build time. The table above is the repro.

## Upstream note

Not reported. A report would give the phase table, the stack samples
and the pair of `RtDepPolyRec`. The public signature of one function
changes (above).
