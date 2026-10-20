# Reussir issues and local patches

This directory records the Reussir problems that lean2rr meets and that
upstream Reussir has not fixed, and the local patches that lean2rr's
builds apply to Reussir.

- **Entries.** One file per problem, `NN-name.md`, where NN is the entry
  number. An entry gives a repro, the cause in Reussir's source where it is
  known, what lean2rr does about the problem and, if there is a patch, the
  patch explained, with its review. Each entry is a numbered *issue*; its
  [kind](#kinds) says whether it is a bug.
- **Patches.** [`patches/`](patches/) holds the patch files.
  [`patches/series`](patches/series) gives the order in which to apply
  them ([applying the patches](#applying-the-patches)).
- **Repros.** [`repros/`](repros/) holds the repro programs and `run.sh`,
  which builds and runs them ([running the repros](#running-the-repros)).

**Base.** lean2rr's Reussir is upstream Reussir `7954a367` (`main` on
2026-10-19) plus the 9 patches of the series. The checkout at
`./reussir` is not part of this repository; its branch `l2r-base3`
(head `4c490260`) is that stack (the series gives the same tree,
`cc4a28d9`), and `scripts/l2r.py` stops with an error on a Reussir
without it ([applying the patches](#applying-the-patches)).

The base before it was `./reussir`'s branch `l2r-base2` (head
`b2e4a47e`): upstream `943f2195` plus 35 patches. Those 35 patch files,
and the entries this directory had before 2026-10-19, are in git history
and in that branch. On 2026-10-19 every entry that `7954a367` fixes was
deleted and the rest were renumbered
([history](#history-the-renumbering-of-2026-10-19)). Old entry 31,
deleted at first, came back the same day as entry 16 (upstream fixes it
only in part).

## Names

- **Entry numbers** run from 1 to 16. The next free number is 17. (Old
  number 37 was reserved for another track's patch, value records across
  the FFI boundary; that track takes the next free number.)
- **A patch file** is named `NN-x-slug.patch`. NN is the number of its
  entry. The letter x gives the order of the entry's patches (a, b, c,
  ...). The slug is a short description. Every patch belongs to exactly one
  entry. In the text, a patch is named by NN-x: 02-b is the second patch of
  issue 2.
- **Patch file contents** are `git format-patch` output of the commits of
  `l2r-base3` (made as branch `l2r-move`), against `7954a367`. A file's subject line is the subject of
  its commit, and these subjects use the old numbers: "bug 13", "13b" and
  "issue 13" mean entry 2, "bug 27" entry 2 (patch 02-d), "bug 34" entry 5,
  "issue 38" entry 7; the subjects of 09-a and 10-a have no number. The
  [history](#history-the-renumbering-of-2026-10-19) maps old numbers to
  new ones.
- Older text says "bug NN" for every entry, whatever its kind: read it as
  "issue NN". Text inside the entries that names an entry or patch deleted
  on 2026-10-19 says "old NN" with the upstream pull request that fixed it.

## Kinds

Only a *bug* is erroneous behaviour. Every other kind is correct
behaviour by Reussir's own rules and promises: rrc's output is right. A
patch for an issue that is not a bug is an improvement (an optimization or
a feature), not a fix.

- *bug*: reproducible, erroneous behaviour: a crash, a wrong result, valid
  code rejected, a broken build or broken build artifacts. Nothing else.
  Its patch is a fix.
- *cost*: correct, but slow or big (build time, memory, run time; also
  debug output). Its patch, if any, is an optimization.
- *missed optimization*: correct output, slower than it could be. Its
  patch, if any, is an optimization.
- *missing feature*: something Reussir never promised that lean2rr needs
  (frees in native Lean's order, a hook at the end of a free, handles that
  may be a number). Its patch is a feature.
- *issue (dependency)*: an error in a library that Reussir pins, not in
  Reussir's own code (15: mimalloc v2.2.4). lean2rr works around it
  outside Reussir; the change on Reussir's side is a newer version of the
  dependency.

## Status

One row per entry, grouped by kind. Column *Patches*: the entry's patch
files in the series, or "none", or a parked patch
([parked patches](#parked-patches)). Column *Upstream*: what upstream
`7954a367` does about it (checked 2026-10-19 where it says so).

| # | Kind | Effect | Affects lean2rr output? | lean2rr workaround | Patches | Upstream |
|---|---|---|---|---|---|---|
| [5](05-executable-textrel.md) | bug (link) | `rrc --emit executable` compiles static code but links a PIE: text relocations (GNU ld), a link error (lld, and on x86-64) | yes without the workaround | `scripts/l2r.py` passes `--relocation-mode pic` | [05-a](patches/05-a-pic-by-default.patch) | not fixed (pull request #758 open) |
| [12](12-nullable-as-ref.md) | bug | reussir-rt's `Nullable::as_ref` returns a reference to a local copy of the pointer word (dangling) | no: nothing calls it | - | none | unchanged; repro fails (checked) |
| [13](13-small-allocation-limit.md) | bug (32-bit targets) | constant-size boxes of 513 to 1024 bytes go to `mi_malloc_small`, whose limit is 512 bytes there | no: 64-bit targets only | - | none | unchanged (checked) |
| [14](14-polyffi-rc-substitution.md) | bug (hand-written MLIR only) | a polymorphic-FFI substitution given as an MLIR rc type becomes Rust's `Rc` without the record's glue | no | - | none | not rechecked |
| [16](16-driver-stack-address-limit.md) | bug (under `ulimit -v`) | rrc's 1 GiB driver stack (#686) counts against an address-space limit: under `ulimit -v` 1250000 or 1600000 rrc aborts where it compiled before | no: lean2rr sets no such limit | - | none (parked: [16-a](patches/parked/16-a-driver-stack-rlimit.patch)) | open: #686 is the old 31-a; no pull request planned |
| [3](03-value-record-dag.md) | cost (deliberate design) | the first acquire/drop expansion writes a `[value]` record's copy out in line, exponential for records shared in a DAG | no, lean2rr's `[value]` records are shallow | - | none | still reproduces (checked) |
| [4](04-emit-mlir-size.md) | cost (debug output) | the `--emit mlir` dump is exponential in the nesting of records that share sub-records | no, builds unaffected | dump smaller programs | none | still reproduces (checked) |
| [11](11-drop-run.md) | cost (run time) | a host frees one cell through 02-b's stack with a deferral and a drain: three calls, a push and a pop | yes, speed (about 5% of monadic-interp's instructions) | none possible | none (parked: [11-a](patches/parked/11-a-drop-run.patch)) | n/a: upstream has no such stack |
| [1](01-phantom-reuse-donor.md) | missed optimization | token reuse picks decrements that never free | yes, speed | fields bound lazily (`lazy-fields`) | none (parked: [01-a](patches/parked/01-a-sink-bound-retains.patch)) | not rechecked |
| [6](06-trampoline-inline.md) | missed optimization | a texture's import trampoline has no inline attribute: at a cold call site a texture costing more than 45 stays a call | yes, speed (three reads at cold sites) | read textures kept small | none (parked: [06-a](patches/parked/06-a-inline-small-textures.patch), [06-b](patches/parked/06-b-inline-guards.patch)) | still reproduces (checked) |
| [8](08-alias-release-donor.md) | missed optimization | token reuse takes the release of a value an opaque call returned (an alias, never freed) as the donor | no longer | a field put back into a rebuilt node is boxed again | none | still reproduces (checked) |
| [2](02-native-drop-order.md) | missing feature (partly fixed upstream) | drop glue does not release in native Lean's order and has no stack a host can share | yes: release order of resources; leanrt needs the stack to build | none | [02-a](patches/02-a-release-chains-in-loop.patch), [02-b](patches/02-b-pending-release-stack.patch), [02-c](patches/02-c-cheaper-pending-stack.patch), [02-d](patches/02-d-defer-nullable-member.patch), [02-e](patches/02-e-last-field-order.patch) | the stack depth is fixed (#677 to #679, another design, first field first); the order and the shared stack are not |
| [7](07-tagged-top-bits.md) | missing feature | the inline count increment of a `tagged` handle uses all 64 bits as the address | yes: the one-word `Box` needs it | none | [07-a](patches/07-a-tagged-top-bits.patch) | not fixed |
| [9](09-drain-end-hook.md) | missing feature | Reussir's runtime does not tell the host when a drain ends | yes: `sync` dependents of a promise released inside a free | none | [09-a](patches/09-a-drain-end-hook.patch) | not fixed (upstream has no drain) |
| [10](10-tagged-ffi-objects.md) | missing feature | an opaque FFI handle must be a pointer to a counted box: it cannot be an immediate | yes: the one-word `Nat` and `Int` need it | none | [10-a](patches/10-a-tagged-ffi-objects.patch) | not fixed |
| [15](15-mimalloc-arena-purge.md) | issue (dependency: mimalloc v2.2.4) | mimalloc's delayed arena purges do not run | yes, peak memory | leanrt sets `arena_purge_mult` to 0 on v2.1.8 to v2.2.7 | none (a newer `libmimalloc-sys` parked) | unchanged (still 0.1.44; checked) |

**Counts.** 16 entries: 5 bugs, 3 costs, 3 missed optimizations, 4
missing features, 1 dependency issue. 5 entries have patches in the
series, 9 patch files in all (five for entry 2, one each for 5, 7, 9 and
10): 1 bug fix and 8 features. 5 parked patches lie outside the series
(01-a, 06-a, 06-b, 11-a, 16-a).

Status words used in the entries' summaries:

- *worked around*: lean2rr avoids the construct or works around it.
- *patched*: a local patch fixes it, or for an issue that is not a bug,
  improves it.
- *does not affect lean2rr*: lean2rr never produces the triggering shape.
- *open*: lean2rr can hit it and has no fix or workaround.

## Applying the patches

[`patches/series`](patches/series) lists the patch files, one per line, in
the order to apply them. To make a patched Reussir, from the repository
root:

```sh
git -C reussir checkout -b l2r-base3 7954a367
while read -r p; do
    git -C reussir am "$PWD/reussir-bugs/patches/$p" || break
done < reussir-bugs/patches/series
cmake --build reussir/build --target rrc reussir-rt
```

Checked on 2026-10-19: the series on `7954a367` gives tree `cc4a28d9`,
the tree of `./reussir`'s `l2r-base3` (`4c490260`). The base before it
(`l2r-base2`) was made the same way from the old series on `943f2195`
(git history).

Order and dependencies:

- 02-a, 02-b, 02-c, 02-d and 02-e are one mechanism, in that order: 02-b
  rewrites 02-a's code, 02-c rewrites 02-b's runtime, 02-d extends 02-b's
  deferral to `Nullable` members, and 02-e changes `emitCellRelease`,
  02-b's code as 02-d amended it.
- 09-a changes 02-b's runtime (`drop.rs`): it comes after 02-c.
- 10-a, 05-a and 07-a touch none of entry 2's files. 07-a needs 10-a (the
  tagged handles whose increment it masks).
- The series is the order in which the patches were made, not entry
  order.

What lean2rr needs: its runtime needs 02-b to build (`leanrt::drop` uses
`reussir_rt::drop`); `scripts/l2r.py` stops with an error when the Reussir
checkout lacks 02-a (with upstream's tail-recursive and retcon drops
off), 09-a, 07-a or 02-e (`REQUIRED_REUSSIR_PATCHES`), so plain upstream
fails there; its
prelude needs 10-a (it declares `Nat` and `Int` `tagged`). 05-a has a
workaround in the driver.

**Adding a patch.** Name the file after its entry: `NN-x-slug.patch`, with
the next free letter of the entry (a new problem gets the next free entry
number, 17). Put it in `patches/` and add its name as the last line of
`patches/series`. Write the *Patch* and *Upstream note* sections of the
entry's file, and update the entry's row in the status table. Add a row to
the [review table](#review) when its review is done.

### Parked patches

A parked patch was made and reviewed, but lean2rr's builds do not apply
it: the owner removed it from the series. Its file is in
[`patches/parked/`](patches/parked/), outside
[`patches/series`](patches/series) and the counts above; its entry says
why it is parked and describes the patch.

| Patch | Entry | Kind | Parked | Why | On 7954a367 |
|---|---|---|---|---|---|
| [01-a](patches/parked/01-a-sink-bound-retains.patch) | [1](01-phantom-reuse-donor.md) | optimization | 2026-10-07 | a missed optimization; lean2rr's `lazy-fields` covers it | does not apply |
| [06-a](patches/parked/06-a-inline-small-textures.patch), [06-b](patches/parked/06-b-inline-guards.patch) (review fixes) | [6](06-trampoline-inline.md) | optimization | 2026-10-07 | the gain is too small for a local Reussir patch | do not apply |
| [11-a](patches/parked/11-a-drop-run.patch) | [11](11-drop-run.md) | optimization | 2026-10-07 | the gain is too small for a local Reussir patch | applies with the series |
| [16-a](patches/parked/16-a-driver-stack-rlimit.patch) | [16](16-driver-stack-address-limit.md) | bug fix | 2026-10-19 | lean2rr does not reach the bug | applies to `7954a367` and `l2r-base3` |

The parked files 01-a, 06-a, 06-b and 11-a are against the stacks they
were made on (`ef922049` plus earlier patches of the old series); 16-a
will be against `7954a367`. To park a patch of the series,
move its file to `patches/parked/`, delete its line from `patches/series`,
rebuild the Reussir stack from the series, and update the entry, its row
and the counts.

## Running the repros

[`repros/`](repros/) has one repro per entry that can show its issue with
Reussir alone: a plain Reussir program (`bugNN-name.rr`), a Lean program
built through lean2rr (`bugNN-name.lean`), a small generator
(`bugNN-name.py`) where the program must be large, or a Rust test of
Reussir's runtime sources (`bug12-nullable-as-ref.rs`;
`bug02-unlink-provenance.rs`, which needs Miri: its header gives the
commands, and `run.sh` does not run it). `bug01b-call-before-branch.rr` is
a variant used in issue 1's entry. Entries 9 and 10 have no repro: they
are missing features that show only through a host that uses them, and
their patches carry their own tests. Entries 11 and 13 to 16 have none
either: 11 is a run-time cost of 02-b's stack (its entry gives the
measure), 13 needs a 32-bit target, 14 MLIR written by hand, 15 is
shown by lean2rr's runtime test `RtArenaPurge` (its peak memory, through
`tests/runtime/alloc-check.sh`), and 16 by upstream's own test under a
`ulimit -v` (its entry gives the command). Each repro file starts with what it
shows and the expected output.

    reussir-bugs/repros/run.sh RRC_CHECKOUT [NN...]

builds each repro with `RRC_CHECKOUT/build/bin/rrc`, runs it and prints one
line per repro, `issue NN` and a status: `REPRODUCES` (the documented
behaviour: the bug or the cost), `FIXED` (the expected output or measure),
`OTHER` (something else) or `SKIPPED` (a tool is missing), with what it
saw and, in brackets, the rrc flags. NN is an entry number (`1`, `02`,
...); the default is every entry with a repro. `run.sh` alone prints its
header: the options and the environment. Entry 2's Lean repro needs the
toolchain `lean2rr/lean-toolchain` pins (`scripts/toolchain.sh`; or
`L2R_LEAN_TOOLCHAIN`) and a lean2rr build.

A plain repro is built with

    rrc bugNN-name.rr -o bugNN --emit executable FLAGS \
        --polyffi-rust-path RUSTC --polyffi-libdir RT --polyffi-libdir RT/deps \
        --polyffi-libdir $(RUSTC --print target-libdir)

where RT is the checkout's `build/target-rt/release` and RUSTC the rustc
that built it (the polymorphic-FFI directories, as `scripts/l2r.py` passes
them). "lean2rr's flags" are
`-O aggressive --no-pack-record-members --reuse-across-call`.

### Latest recorded run

On `l2r-move` (now `l2r-base3`: `7954a367` plus the series), 2026-10-19, with dev
`5a65943c`'s lean2rr build, from a scratch directory, with the old
`run.sh` (its numbers in brackets): issue 2 FIXED (list, snoc list and
left spine of 1,000,000 cells on an 8 MB stack; lean2rr `List.replicate`
and snoc list of 40,000,000 cells; 1,000,000 links through `Nullable`
[13, 27]), issue 5 FIXED (no text relocations [34]), issue 7 FIXED
(prints 143 [38]); with the new `run.sh`: issues 3, 4, 6, 8 and 12
REPRODUCES (open upstream too), 2, 5 and 7 FIXED. The same day, upstream alone (`7954a367` plus 10-a,
05-a and 07-a) printed FIXED for the plain repros of issue 2 (the list
shapes and the `Nullable` chain), so its stack depth is fixed upstream; its
Lean repro needs leanrt, which does not build there.

## Policy

- Every Reussir problem lean2rr meets is documented here, with a repro,
  until upstream fixes it. When upstream fixes an entry fully, the entry,
  its patches and its repros are deleted (they stay in git history); an
  entry upstream fixes in part keeps only the part that remains, with a
  reduced patch.
- A real Reussir bug (verified reproducible erroneous behaviour) gets a
  small local patch, reviewed adversarially, even if lean2rr never
  triggers it or works around it.
- Only bug fixes and major items stay in the series (owner, 2026-10-07):
  the bug fixes (05-a) and the features lean2rr needs (02-a to 02-e, 07-a,
  09-a and 10-a). A fix of a bug that lean2rr does not reach is parked (16-a); no
  upstream pull requests after #758 (owner, 2026-10-19).
- A patch that only buys a small run-time gain on a few programs is
  parked, not kept (01-a, 06-a with 06-b, 11-a). Costs whose removal would
  be a redesign (3, 4) and missed optimizations stay unpatched, with the
  reason in their file.
- Patches are local: lean2rr's work does not push them. The "Upstream
  note" at the end of a patched entry is text for an upstream report.
- lean2rr's workarounds stay, so that lean2rr also works with an unpatched
  Reussir. The exceptions are the features lean2rr requires
  ([what lean2rr needs](#applying-the-patches)). The workarounds for
  entries that upstream `7954a367` fixed are listed in
  [`docs/implementation/reussir-workarounds/`](../docs/implementation/reussir-workarounds/README.md)
  as "removable after the move". lean2rr's builds use that base, so each
  can go, one change per workaround, with its test.

## Review

Each patch is reviewed adversarially: code review, differential fuzzing
against an independent reference evaluator, ASan builds (Miri for the
runtime patches), and lean2rr's runtime suite and corpus, in rounds
repeated until one finds nothing. The review notes are local notes,
outside this repository (column *Notes*: their names). The patches were
reviewed under their old names, on the old base:

| Patch (old name) | Round | Notes | Result |
|---|---|---|---|
| 02-a (13-a) | rounds 1 to 3 | `rv-patches/FINDINGS.txt`, `rv-patches/roundN/FINDINGS.txt` | passed (revised, extended after round 2) |
| 02-b (13-b) | round 4 (4, 4b, 4c) | `rv-patches/round4*/FINDINGS.txt` | passed, revised twice |
| 02-c (13-c) | round 5 | `perf0014-review/` | passed; the fix of old entry 47 (pointer provenance, 2026-10-09) checked with Miri (the same machine code), not reviewed yet |
| 02-d (27-a), 09-a (40-a) | RV7-P22 round 2; RV8 | `rv7/p22/round2/FINDINGS.txt`, `rv8/reussir/FINDINGS.txt` | RV7P-05 led to 27-a; no defect in 40-a; RV8R-01 (27-a, release order, low) fixed in the amended 27-a |
| 02-e (13-d) | review-0069 | `review-0069/` | no defect |
| 05-a (34-a) | RV8 bug34 | `rv8/reussir/bug34/FINDINGS.txt` | no defect; N1: obj and staticlib outputs keep the static default (scope note); N2: the .text change is linker veneer padding |
| 07-a (38-a) | review-anybox r1 | `review-anybox/r1` | no defect; the atomic case was added to the patch's test |
| 10-a (41-a) | mem-nat review, RV8 | `mem/nat/review/FINDINGS.txt`, `rv8/nat/FINDINGS.txt` | no defect (the optional hardening is in) |

The rebase onto `7954a367` (2026-10-19) is not reviewed yet: 10-a had two
conflicts (upstream added the `placement` and `launch` fields to
records), 02-a, 02-b and 02-d five small ones (listed in
[issue 2](02-native-drop-order.md#patch)), and 02-b needed one line
(the drain declaration in the shared symbol table). Tested: the repros
above and 13 targeted lean2rr runtime tests (issue 2's entry lists them).

## History: the renumbering of 2026-10-19

Upstream Reussir moved from `943f2195` to `7954a367` (82 commits; pull
requests #656 to #690 carry most of lean2rr's fixes, some in another form,
and #675 to #682 redesign drop glue). The entries that `7954a367` fixes
fully were deleted, with their patch files and repros (all in git
history); the others were renumbered in their old order.

Kept entries, old number to new:

| Old | New | Old | New | Old | New |
|---|---|---|---|---|---|
| 7 | 1 | 36 | 6 | 41 | 10 |
| 13 (with 27 and 47) | 2 | 38 | 7 | 42 | 11 |
| 25 | 3 | 39 | 8 | 43 | 12 |
| 32 | 4 | 40 | 9 | 44 | 13 |
| 34 | 5 | | | 45, 46 | 14, 15 |
| 31 (partly: see 16) | 16 | | | | |

Old 31 (rrc overflowed its stack on deep expressions) is fixed upstream
by #686 (`3e34334f`, the same code as the old 31-a), but that code makes
builds under an address-space limit abort. Entry 16 keeps that part. It
was deleted with the others first and came back the same day, appended
as 16, so it is not in the old order.

Patches, old name to new: 13-a, 13-b, 13-c, 27-a, 13-d to 02-a, 02-b,
02-c, 02-d, 02-e; 34-a to 05-a; 38-a to 07-a; 40-a to 09-a; 41-a to
10-a. Parked: 07-a to 01-a; 36-a, 36-b to 06-a, 06-b; 42-a to 11-a; 03-c
deleted with entry 3. Old 31-a is upstream (#686); its rework is the
parked 16-a. Old 11-b shrank to one line, now in 02-b (the rest
is upstream #671).

Deleted entries (old number: the upstream pull request and commit that
fix it; "same" when upstream has the same code, "other form" when it
fixes the problem with other code):

| Old | Problem | Upstream |
|---|---|---|
| 1 | `[value]` enum payload bytes lost on a move | #663 `823a7b29` (our pull request, other form: a per-byte rule) |
| 2 | in-place reuse skips a field store | #652 `3be77a64` (structures), #656 `c7ab73d5` (variants, other form: by type and byte offset) |
| 3 | slow frees from moved 16-byte allocations | #667 `dce185d2` (other form, plus an alignment fallback) |
| 4 | rrc recurses on equal recursive types | #654 `634fb551` (same) |
| 5 | TokenReuse crashes on a one-armed `if` | #655 `943f2195` (same) |
| 6 | a static cell freed after 2^32 references | #661 `198213ff` (our pull request, other form: plus `rc.is_immediate`) |
| 8 | padding lift larger than Reussir's layout | #658 `e8e85b40` (same) |
| 9 | a member used twice loses a reference | #653 `0ed0f243` (same) |
| 10 | closure devirtualization prints types exponentially | #668 `b314cc81` (other form: bounded named-record expansion) |
| 11 | superlinear SCCP; glue lookups rebuild symbol tables | #669 `514209db` (other form: Reussir's own SCCP pass), #671 `e8583c42` (other form) |
| 12 | cstree swaps colliding syntax nodes | #664 `9031647c` (other form: a collision-safe cstree fork) |
| 14 | a member consumed before the release loses a reference | #653 `0ed0f243` (same) |
| 15 | a `Nullable` match yielding a counted value | #662 `b6981996` (same) |
| 16 | reuse across calls superlinear in match nesting | #672 `4dc9e469` (other form) |
| 17 | `convert-scf-to-cf` rollback memory | #670 `211c97bb` (same code) |
| 18 | the `rrc` target alone does not link | #684 `2d65de01` (same) |
| 19 | a `Cell` of a `[value]` record does not compile | #666 `3f96d206` and #681 `1ec611dc` (other form: no `field` capability for cell payloads) |
| 20 | the inliner follows copied calls into recursion | #674 `892be34c` (other form) |
| 21 | an unterminated `[:` in a texture is dropped | #657 `fec8f033` (same) |
| 22 | a wildcard arm over a wide enum costs N^3 code | #673 `80fd9a99` (other form: equal dispatch arms merged) |
| 23 | polymorphic-FFI modules linked one call each | #683 `29fd3184` (same code) |
| 24 | matrix-exponentiation state ordered by addresses | #685 `2c13e4c8` (same code) |
| 26 | `assume(launder(p) == p)` lets LICM hoist stores | #651 `5776bbe5` (same) |
| 27 | a chain through `Nullable` recurses once per link | #677 `f5818312`, #679 `20a6dd3d` (other design); 27-a lives on as 02-d |
| 28 | `-O aggressive` unique-carrying join | #660 `4c79708a` (same) |
| 29 | `--emit mlir` of an `#[ffi]` member does not parse back | #665 `5ae43a9a` (other form) |
| 30 | call lowering scans the module once per call | #687 `20c67786` (other form) |
| 33 | the rc and ref type parser drops trailing text | #659 `cf175cf4` (same) |
| 35 | rustc runs again for every texture | #690 `84336b63` (other form: `llvm::localCache`, the same `REUSSIR_FFI_CACHE_DIR`; entries `llvmcache-*`, mode 0600, pruned when not read for a week or above 1 GiB in all). #690 lacks the old patch's FCR-03 fix: a `%` in the directory path silently stops storing (reproduced on 2026-10-19). lean2rr's paths have no `%` |
| 47 | 13-c's `unlink` used another cell's provenance | never upstream: a bug of our own patch, fixed in it (02-c) |

Notes on the deleted entries, from the 2026-10-19 check on `l2r-move`:
their repros printed FIXED (22 by hand: N = 30 in 2.6 s), except 24 and
30 (not run: they need `reussir-llvm-opt` and `reussir-opt`) and 17. Old
issue 17's repro prints REPRODUCES on the new base and on `l2r-base2`
alike (each `let` costs 0.10 MB up to 250 lets and 0.25 MB from 250 to
500): lean2rr's output changed since its threshold was set (the 250-let
and 10-let executables have almost the same size), so it no longer
measures the long block; upstream has 17-a's code. lean2rr's workarounds
for the deleted entries stay until each is removed (see
[Policy](#policy)).

The four-digit patch numbers of older notes (0002 to 0069, before
2026-10-06) map to the old names of the patches: 0013 to 0015 are 13-a to
13-c, 0027 is 27-a, 0040 is 40-a, 0050 is 41-a, 0065 is 34-a, 0068 is
38-a, 0069 is 13-d; the others belong to deleted entries (the old table
is in git history).

## Glossary

- **Cell** (or box): a heap object with a 32-bit reference count in its
  header. A *fused* variant box keeps the count and the variant tag in one
  8-byte header word.
- **Retain / release**: `reussir.rc.inc` / `reussir.rc.dec`. A release
  expands (`RcDecrementExpansion`) to "count == 1: drop the contents and
  keep the cell as a token; else count - 1".
- **Token reuse**: the cell freed by a release is offered as a *token* to a
  later allocation of the same size, so the construction writes into the
  old cell (Reussir's version of Lean's reset/reuse; pass `TokenReuse`).
  `--reuse-across-call` lets tokens live across non-tail calls.
- **Destructuring decrement**: a release of a match's scrutinee tagged by
  `RcDispatchFusion` with the arm's tag and the "bound" members. The
  members move to the arm's variables instead of being retained one by one.
  It is Koka's `dropn_reuse` shape.
- **Drop glue**: the per-type functions that release a record's contents
  (`drop_in_place`, made by `AcquireDropExpansion`).
- **Immediates / TBI**: nullary constructors (`Nil`, `Leaf`) of shared
  enums are not allocated. Each is a tagged pointer to a static dummy box.
  TBI (aarch64's Top Byte Ignore) lets such a pointer carry the tag in its
  top byte and still be dereferenced.
- **Texture**: the Rust body of an `#[ffi(import)]` function; a polymorphic
  one is compiled by rustc once per instance.

## Other observations

- **Tagged pointers from the allocator.** Under top-byte tagging, a pointer
  with a nonzero top byte is an immediate. An allocator that tags real
  pointers (memory tagging, HWASan) would make real cells look like
  immediates: their decrements are skipped (a leak). The allocator lean2rr
  uses returns untagged pointers, and the sanitizer modes use the untagged
  encoding. Not reproducible on the test machine (no MTE). (Review round 1,
  RV-6.)
- **Finalization order.** Values are not always released in the order of
  native Lean's `lean_del`. The difference is observable when releasing
  objects has effects, for example file handles that flush buffered output
  when dropped. With 02-b the order is Lean's in every free that starts at
  a container, and mostly below the first cell of a free that starts at a
  record ([issue 2](02-native-drop-order.md); plan §10).
- **Drop glue that may not return.** Reussir marks drop glue `mustprogress
  nounwind willreturn`. Through lean2rr's runtime (`leanrt::drop::run`,
  and the drain hook of [09-a](09-drain-end-hook.md)) a free can run Lean
  continuations, which might not return (`IO.Process.exit` inside a sync
  dependent), which would falsify `willreturn`. No concrete miscompile was
  found. (Review RV8, side note on 40-a, now 09-a.)
- **TokenReuse's locality bonus is dead code (not a bug).** In
  `lib/Transformation/TokenReuse/TokenReuse.cpp`, function `heuristic`,
  the walk from a new cell's field back to the cell it was loaded from
  steps to `dispatch.getValue()` where the scrutinee (`getVariant()`) is
  meant, and the field list it starts from is read from the `rc.create`
  itself, so the list is always empty and the bonus never applies (a
  missed optimization; with only the first mistake corrected,
  `reussir-opt --reussir-token-reuse` crashes on a result-less dispatch).
  Not rechecked on `7954a367`. [Issue 8](08-alias-release-donor.md) is a
  case where the bonus would decide for the matched cell.

## Missing features that cost lean2rr performance

Not bugs, but each one costs lean2rr measurably:

- **Borrowed parameters.** Reads of arrays and strings through the runtime
  take the container owned, so each read retains and releases it.
  Traversals that keep unchanged nodes pay the same on fields (about 1.5x
  native on an `Expr.replace`-style DAG traversal).
- **A one-word `Nat`** (done locally: [issue 10](10-tagged-ffi-objects.md),
  patch 10-a, tagged opaque handles; `Nat` and `Int` are one tagged word,
  as natively).
- **`[value]` types across the FFI.** Arrays of enumerations or `[value]`
  records need runtime-side representations or wrappers.
- **Guaranteed tail calls.** Mutual tail calls are sibling calls only when
  all arguments fit in registers.
