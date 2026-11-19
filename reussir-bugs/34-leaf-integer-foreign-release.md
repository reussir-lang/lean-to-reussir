# 34. A record of scalars and integers that foreign code releases enters a destruction scope

**Kind:** cost (run time). Not a bug: the program is correct. When Rust
code releases the last reference to a Reussir record whose members are
scalars and big integers (`Nat`, `Int`), the release goes through the
runtime's destruction scope. Its body releases the integers in place
and frees the box, so it has no use for the scope. Patch 34-a lets such
a release keep its direct body. It is an optimization, and it widens
the rule of patch 31-a ([entry 31](31-leaf-foreign-release.md)).

## Summary

**Kind:** cost. **Status:** patched (34-a), patch 12 of the series on
upstream `36a55a0f` (Reussir branch `l2r-base13-r7`, tree `6dc99546`; 2 files, +109/-2: code +19/-2 and one test of 90 lines).
`scripts/l2r.py` does not check for the patch: without it the programs
are the same and one kind of release is slower. The gate on the series
with it passed (gate 57, 2026-11-18).

**Upstream (2026-11-18):** Open at `36a55a0f`: new with upstream's drop
series of 2026-11-01, as entry 31. On `l2r-base12` the same release was
direct code. Not reported: the maintainer takes changes from this
directory. The patch needs 31-a (the rule that it widens) and 32-a (the
class that it uses); it does not apply to a clean `36a55a0f` alone.

## Context

- **A foreign release and its bridge:** see
  [entry 31](31-leaf-foreign-release.md#context). For a record type
  that Rust code holds, rrc makes a release function; upstream's
  worklist drops wrap it, so that the last release calls
  `__reussir_drop_join_or_run(object, worker)`, which sets up a
  destruction scope around the worker.
- **31-a's rule** leaves out a payload that is trivially copyable. A
  big integer (rcgmp) is not trivially copyable: it can be a heap
  value with a count.
- **The leaf class.** Since 32-a
  ([entry 32](32-integer-members-drop-path.md)) the worklist glue
  releases integer members in place, with no cleanup hook, and has a
  class for payloads of scalars and integers (`WorklistGlue::classify`,
  the result `Leaf`).

## Symptom

One case of the shared benchmark set, L08 unionfind: 293.1 ms on
`l2r-base12`, 315.7 ms on the series of 16 patches (1.077, min 1.050;
timing run 23). The `.rr` is identical on both sides.

unionfind keeps its nodes as a record of two `Nat`s in an array. A
sampler shows `reussir_rt::drop_stack::run` with 7% of the samples on
the new base; the old base does not have it. The function that drops
an array element:

- on `l2r-base12`: decrements, releases the two integers in line
  (`rcgmp_mpz_free` for a big one) and tail-calls the deallocation;
- on the series of 16: decrements and tail-calls
  `__reussir_drop_join_or_run` with the release's worker. The worker is
  the old in-line code.

Counts at run time (size 300000): 665,008 allocations on both sides;
destruction scopes entered: 0 on the old base, 665,000 on the series,
one for each freed record. From this case one scope entry costs about
3 ns.

## Cause

`prepareWorklistDropBridges`
(`lib/Conversion/AcquireDropExpansion/WorklistDrop.cpp`) with 31-a
keeps the body of a foreign release only when the payload is trivially
copyable. A record with an integer is not, so it gets the bridge. But
its worker puts nothing on the work list and runs no cleanup hook: it
releases the integers (which never defers and never enters a scope)
and frees the box.

## lean2rr

lean2rr reaches it where a record of scalars and integers is an element
of an array or lives in another runtime container. The reach is wide,
mostly through library records: 345 of the 742 executables of the
runtime suite and 20 of the 53 benchmark programs lose at least one
release worker with 34-a. Of the 53 benchmark cases one shows it in
time (L08). Foreign releases
that get a direct body with 34-a, in programs that were compared
function by function:

| Program | bridged releases, before to after | Types that change |
|---|---|---|
| L08 unionfind | 8 to 7 | `nodeData(Nat, Nat)` |
| L15 monadic-interp | 15 to 14 | `Std.Legacy.Range(Nat, Nat, Nat)` |
| L18 hashmap | 11 to 10 | `Point(Int, Int)` |
| Z01d lean-zip decompress | 23 to 19 | `IO.FS.SystemTime(Int, u32)`, `Std.Legacy.Range`, a configuration record of five `Nat`s and a `bool`, and the variant `LZ77Token` |
| X07, L12, L01 | unchanged | none |

In each program one release worker for each changed type goes away,
and the runtime functions that inline the release change with it
(`array::drop_record`, `drop::free_vec`, `drop::step_vec`). Nothing
else differs.

## Patch

[`patches/34-a-leaf-integer-foreign-release.patch`](patches/34-a-leaf-integer-foreign-release.patch),
`[drop] release a foreign box of scalars and integers in place`.

A new predicate, `WorklistGlue::releasesInPlace(payload)`, replaces
`isTriviallyCopyable` in 31-a's condition. It holds for:

- a payload of the leaf class: scalars, integers, and value records of
  them;
- a complete variant whose arms are all such leaves, and of which no
  arm is a field.

A trivially copyable payload is a leaf, so 31-a's cases are kept. The
rule is for the box type as the foreign release sees it: a variant
with one arm that holds a box is bridged as a whole. A record with a
box member, with a foreign object (also a tagged handle) or with a
nullable member keeps the bridge, and so does a regional box.

**Why a separate patch, after 32-a.** The rule needs 32-a's class, and
31-a comes before 32-a. 32-a is at 299 changed lines, and the rule
with its test is 111 lines (the series keeps each patch at 300 changed
lines or fewer). The other choices change the order of two patches
that are reviewed and gated, or their text. With 34-a, the files of
31-a and 32-a are byte-identical to before.

**Why the behaviour is the same.** The body that stays is the ordinary
release of user code: a decrement; at the last reference a call of the
record's direct drop helper, which has only releases of integers and
no drop-stack operation (checked); and the free of the box. It
decrements no other box and runs no hook. So there is nothing to
order, and the code is the same under both drop orders. The release of
an integer never defers and never enters a scope: the runtime's
function decrements and deallocates, and no file of the integer
library names the drop stack.

| Case | Result | How checked |
|---|---|---|
| a record of integers and scalars | direct | lit, both orders |
| a record of value records with integers | direct | lit |
| a variant whose arms are all leaves (also a nullary arm, an immediate under TBI) | direct | lit; run |
| a variant with one boxed arm | bridged, the whole type | lit |
| a record with a box member | bridged | lit |
| a record with a foreign object (so also a tagged handle) | bridged | lit; tagged by reading |
| a nullable argument; a nullable member | bridged | read |
| a rigid or flex box | left out, as in 31-a | 31-a's lit case, the same condition |
| an atomic box | the checker refuses an `Arc` of a record with an integer; in MLIR written by hand the body is the atomic decrement and the same helper | read |

**Difference from the timed prototype.** The prototype (5 lines)
tested the leaf class only, which never holds for a variant. 34-a also
takes a variant whose arms are all leaves.

**Tests.** `conversion/worklist_drop_bridges_integers.mlir` (needs
rcgmp): three direct and three bridged cases, under both drop orders.
It fails without the code change and passes with it.

## Review

Accepted by an independent reviewer (local notes `port13/reviews/RV2`,
the section on 34-a). The reviewer could not break it.

- **Integers held by Rust containers (run).** A Rust `Vec` of eight
  element types (records of integers, nested value records, variants
  with leaf arms and with boxed arms, records with a box, with a
  handle, with an in-line array of integers), with small and heap
  integers, in 54 scenarios (dropped whole, element by element, after
  a copy, an element replaced, an element that outlives the vector),
  with a wrapper that tracks every integer allocation. Two
  optimization levels, both drop orders, pristine upstream against the
  patch's base form and the series against the series with 34-a: 0
  integers left alive and 0 bad frees in all 16 runs. Results,
  allocation counts and hook order are equal before and after in every
  scenario. Scope entries for each scenario: 12 to 0, 12 to 0 and 10
  to 0 for the three leaf types; unchanged for the five others.
- **The boundary of the leaf class (run and read).** Direct: value
  records nested two deep, a variant of leaf arms, an atomic box.
  Bridged: a nullable box, a token, an in-line array of integers, a
  handle inside a nested value record, a variant with such an arm. No
  direct body and no drop helper of one has a drop-stack operation.
- **lean-zip (run).** The program holds the variant that only 34-a's
  form covers. Built on the series with 34-a, its compress and
  decompress cases print native's results (one run each; not timed).
- **The timed code.** L08 built with 34-a has the same instructions as
  the prototype's build (234,996 lines of disassembly, equal after
  addresses, immediates and symbol names are masked).

Findings, all low or information:

- **H1.** The lit test has no case for a handle inside a nested value
  record, the shape where a shallow rule would be wrong. The
  reviewer's own probe covers it.
- **H2** (upstream's design, not this patch). Under TBI a nullary arm
  crosses to Rust as an immediate; the direct body reads the count
  before it tests for an immediate, as upstream's bridge does. An
  immediate is never decremented, dropped or freed.
- **H3.** The timing pair is the prototype's and covers records. The
  variant part is checked for correctness, not timed.

Formatting: the patch's changed lines are clean under clang-format
23.1.0 (LLVM style) since 2026-11-19 (the formatter moved line breaks
in 6 lines and changed no token).

Not verified: a byte comparison of upstream's units against the
series without 34-a (no such build exists any more; the reviewer's
argument is that six units have no foreign release function and the
seventh, `std`, has only 31-a's case); tagged handles as members by a
run; wasm; sanitizer runs.

## Measured claim

**Wall time** (timing run 23, 2026-11-18: the series of 16 patches
with the prototype against the same without it; direct pairs, median
of 9 and min, the two sides in turn; 14 cases; all outputs equal):

| Case | without | with the prototype | ratio (median) | (min) |
|---|---:|---:|---:|---:|
| L08 unionfind | 315.3 ms | 295.6 ms | 0.938 | 0.934 |
| the 13 others | | | 0.997 to 1.004 | |

The old base's time for L08 is 293.1 ms, so the case is back within
about 1% of it (derived: 1.077 times 0.938 is 1.010; not a direct
pair). Scope entries at size 300000: 665,000 to 0.

These numbers are the prototype's. 34-a compiles L08 to the same
instructions (above).

**34-a itself, on the full set** (timing run 24, 2026-11-18/19: the
series of 17 patches against the series of 15, which differ in 33-a,
which changes no generated code, and 34-a; direct pairs, median of 9
and min, the two sides in turn; 53 cases; the `.rr` byte-identical on
both sides; all outputs equal):

| | with 34-a / without |
|---|---|
| geometric mean, 53 cases | 0.999 |
| outside ±3% | one case, faster: L08 unionfind 0.937 (315.6 ms to 295.6 ms; min 0.938) |
| slowest | E10 closure_pipeline 1.022 (inside the band; its min is 0.999) |
| the 20 cases whose program loses a release worker | 0.996; without L08 and one bimodal case (0.985), the 18 others are between 0.994 and 1.006 |
| the 33 others | 1.001 |
| peak memory | 1.000; no case outside 3% |
| `.text` of the executables | 1.000; between -0.3% and +0.6% |

A repeat of six pairs at the end of the session gave L08 0.936. So
34-a makes unionfind 6.3% faster and moves no other benchmark case
measurably, in time, peak memory or code size, though it changes the
release path of 20 of the 53 programs. Against `l2r-base12`, a direct
pair on the series with 34-a: L08 1.010 (1.077 before).

The records that change in the 20 programs: `IO.FS.SystemTime` (10
cases), `Std.Format.SpaceResult` (8), `Std.Legacy.Range` (7), two
types of lean-zip (4 each, one of them the variant), `Rat` and records
of `Std.Time` (3 each), and one record each in L08, L18 and one more
case. The rule for variants of leaf arms has no timing of its own: it
is checked for correctness, and the cases that hold such a variant
(lean-zip's) are among the 18 that do not move.

**Leaks:** the author's harness (a Rust `Vec` of records and of a
variant with heap integers; two levels, both orders, before and after:
eight runs): 0 integers left alive, 0 bad frees; scope bridges 1,001
before, 0 after. The reviewer's 16 runs: above.

**Other code:** upstream's benchmark suite, core and std (33 units):
no unit changes through 34-a by the author's counts (the base form
differs from pristine in the same three units as 31-a and 32-a, with
31-a's counts of bridges). This is an argument from counts, not a
byte comparison against the series without 34-a.

**Reussir's tests** (pristine with 31-a, 32-a and 34-a): lit, the drop
and integer subsets, 120 pass of 136 selected, 15 unsupported, 1
failure that is upstream's own on this machine
(`region_drop_policy.mlir`); 97 of 97 unit tests.

**Through lean2rr:** 12 release-order, memory and integer tests of the
runtime suite pass on the series with 34-a (author). The gate on the
series of 17 patches (gate 57, lean2rr dev `f20aed74`) passed: 748 of
750 runtime tests with 2 expected failures, 23 of 23 check scripts,
the classic corpus in its three modes, the raytracer. Against the gate
on 16 patches:

- all 742 `.rr` files are byte-identical;
- 345 of the 742 executables differ in `.text`, and each of them has
  lost at least one `<Record>_ffi_release.worklist.backward` function
  (465 functions, 100 to 216 bytes each); the 397 others are equal in
  every section size;
- the records are mostly the library's: `StdGen` in 123 programs,
  `Std.Format.SpaceResult` in 98, `Std.Legacy.Range` in 90,
  `IO.FS.SystemTime` in 73, two records of `Float.Model` in 16 each,
  and about 30 user records in 1 to 6 programs each. 85 programs lose
  only `StdGen`'s function;
- in 15 programs leanrt's generic code for such records grew, where an
  array or a runtime cell holds them (`drop::free_vec`,
  `drop::step_vec`, `array::drop_record`, `drop::release_record`): the
  direct release is inlined there. The largest growth seen is in
  `RtArraySets` (+532, +760 and +148 bytes in three functions). The
  benchmark programs show no such growth in size (at most +0.6% of
  `.text`);
- `alloc-check` (81 tests, 191 rows): no row moves beyond the noise
  between runs (4 allocations); the scripts that pin shapes, counts
  and hashes have the same output.

**Not measured:** the rule for variants in a timing step of its own;
the suite's tests in time (the gate checks results).

**Repro.** [`repros/bug34-integer-leaf-foreign-release.mlir`](repros/bug34-integer-leaf-foreign-release.mlir), `run.sh`'s `bug34`. It was added after gate 57's `run.sh`. In a run after the gate, from this branch, on a `reussir-opt` built for the series' tree and on pristine `36a55a0f`: FIXED on the series, REPRODUCES on pristine. The gate itself ran the patch's lit input by hand through `reussir-opt` (backward order): 6 bridge functions on pristine, 3 with 34-a (on a build of pristine with 31-a, 32-a and 34-a).

## Upstream note

Not reported. A report would give the two forms of the element drop,
the count of scope entries and the pair of L08. The fix is one
predicate next to 31-a's rule, built on 32-a's class.
