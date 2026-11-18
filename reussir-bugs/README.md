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

**Base.** lean2rr's Reussir is upstream Reussir `36a55a0f` (`main` on
2026-11-17) plus the 12 patches of the series: 10-a, 07-a, entry 20's
five (20-a, 20-g, 20-c, 20-d, 20-e), 21-a, 29-a, and one fix for each
of the three upstream bugs that the port found (26-a, 27-a, 28-a). The file
[`patches/base`](patches/base) holds the full id of the upstream commit.
The Reussir checkout is not part of this repository. Its branch
`l2r-base13-final` (head `d62797ac`, tree `9066f3fc`) is that stack:
the compiler that lean2rr's final gate ran on. The series of this
folder gives tree `ccdf369d` (checked on 2026-11-18, `git am
--keep-non-patch` on a clean `36a55a0f`). The two trees differ in one
test file of 29-a, which was amended after the gate's compiler was
built (+6/-8 lines); no compiler source differs
([entry 29](29-texture-store-open.md)). `scripts/l2r.py` stops
with an error on a Reussir that lacks the upstream drop interface or a
patch that lean2rr requires
([applying the patches](#applying-the-patches)). The build needs GMP and
newer build tools ([building Reussir](#building-reussir)). Every patch
has a measured claim
([what each patch buys](#what-each-patch-buys-and-how-it-was-measured)).

How the base moved from `l2r-base12` (upstream `95d9a1c8` plus 24
patches) to this one
([history](#history-the-move-to-36a55a0f-2026-11-17)):

- **Upstream took worklist drops.** Its series of 2026-11-01 (#872 to
  #914) deleted the retcon drop lowering and added scoped drop worklists
  in `crates/reussir-rt/src/drop_stack.rs`. This is the design of entry
  23, so the sixteen patches 23-a to 23-p left the series
  ([issue 23](23-worklist-drops.md) has the mapping). rrc's option
  `--drop-order forward|backward` selects the order of releases; the
  default, `backward`, is the order that `l2r-base12` gave, and
  `scripts/l2r.py` passes it explicitly.
- **Upstream closed the four issues we filed.** #759 and #760 (retcon
  drops: entries 19 and 23) closed on 2026-11-01 with the removal of
  retcon drops; #761 (the drop executor's slot table) closed on
  2026-10-21; #762 (borrowed parameters) closed on 2026-11-01 with the
  borrow analysis (#854 to #866, #919), which is on by default at the
  optimizing levels.
- **The maintainer's port.** Reussir's maintainer moved lean2rr to
  upstream `44abd17c` (2026-11-04) in lean2rr's pull request #4: leanrt
  on upstream's drop scopes, and a series of 8 patches (10-a, 07-a,
  20-a, 20-c, 20-d and three new ones named 24-a, 24-b, 24-c). He left
  20-b, 20-e and 21-a out of the series.
- **Our move to `36a55a0f` (2026-11-17).** The 8 patches were moved to
  `36a55a0f`, two more sites of 10-a's rule were fixed, and 24-a, 24-b
  and 24-c were folded into the patches that they change. No patch has
  the number 24 now (entry 24 is another topic).
- **The refinement and the final series (2026-11-18).** The five
  patches were reviewed and refined (20-g split from 20-a), 20-e and
  21-a came back with measurements on this base, and three upstream
  bugs got an entry and a fix each (26, 27, 28).
- **mlir-rcgmp.** Upstream's build fetches mlir-rcgmp at `dee6c102`
  (2026-11-14). `l2r-base12` used `cc73b218`.

Status of the port (2026-11-18): **the final gate passed** (lean2rr
`8d032fdb` on Reussir `d62797ac`).

- Runtime suite: 748 of 750 tests identical to native, 2 expected
  failures (`RtCastMixedRebox`, `RtLeanUnsupported`, as before), no
  failure, no rrc crash.
- Check scripts: 23 of 23. Classic corpus: passes on, 26 passes off
  (small and medium sizes) and `unread-fields` (small), 18 programs
  each. Raytracer: 3 of 3, images identical to native.
- `repros/run.sh` on the series and on pristine `36a55a0f`: every
  verdict as its entry expects
  ([latest recorded run](#latest-recorded-run)).
- Reussir's own tests on the series: 174 of 189 selected lit tests
  pass, 15 cannot run on the build machine, 0 fail; `reussir-ut` 97 of
  97.
- The first gate of the port, one day before, ran on the first series
  (5 patches) with the translator of dev: 739 of 747, with 6
  release-order failures and one failing check script
  ([history](#history-the-move-to-36a55a0f-2026-11-17)).
- Wall time of lean2rr's programs against `l2r-base12` and native:
  pending the timing run.

### Earlier bases (history)

The paragraphs below describe the bases before `36a55a0f`. They are
history: the branches they name are in the old Reussir checkout.

`l2r-base12` (head `c1170ff9`, tree `af82b837`) was upstream `95d9a1c8`
(`main` on 2026-10-26) plus 24 patches: 10-a, 07-a, entry 20's five
(20-a, what was left of 20-b, 20-c to 20-e), 21-a and entry 23's
sixteen.

`l2r-base12` was `l2r-base11` (head `a39e59b0`, tree `eb79e76e`) moved
to upstream `95d9a1c8`, which has our pull requests #824, #843 and #845
(20-b's code, split in three) and #844 (20-f's pin): 20-f left the
series, 20-b keeps only the reviewed patch's tests that the pull requests
left out, and rrc and reussir-rt are the same as on `l2r-base11`
([history](#history-the-move-to-95d9a1c8-2026-10-26)). `l2r-base11` is
`l2r-base10` (head `0bea9c7d`, tree `707daa79`) plus 20-f, which moved
the commit of mlir-rcgmp that the build fetches to a faster upstream one
([history](#history-the-mlir-rcgmp-pin-2026-10-26)). `l2r-base10` is
Phase 2's base (2026-10-26). On these bases Reussir freed Direct and
TailLoop records with upstream's glue and the other recursive records
through the per-thread drop stack of entry 23 (worklist drops), its
pending records linked through their own headers on a change of release
function (23-n to 23-p), and lean2rr's runtime kept its pending
releases on that same stack (23-k to 23-m). `./reussir`'s branch
`l2r-base9-shared` (head `6111586c`, tree `8b8dd1cb`) is the same series
without 23-n to 23-p, and `l2r-base9` (head `fc9c1d20`, tree
`8c53abcf`) also without 23-k to 23-m
([history](#history-linked-pending-records-2026-10-26)). So the local
drop patches 02-a to 02-e and the drain-end hook 09-a left the series,
entries 9 and 11 were deleted and their numbers retired, entry 19
(upstream #759) is recorded with its patch parked, and entries 23 and
24 are new
([history](#history-phase-2-worklist-drops-instead-of-the-local-drop-patches-2026-10-25)).

Before Phase 2 the series had 14 patches: 02-a to 02-e, 09-a, 10-a,
07-a, step D's 5 (entry 20,
[history](#history-step-d-patches-published-2026-10-25)) and 21-a
([history](#history-entry-21-2026-10-25)). `./reussir`'s branch
`l2r-base8` (head `8e9a6293`, tree `10b34f74`: `l2r-stepd` plus 21-a)
is that stack, `l2r-stepd` (head `e3b96e03`, tree `b3b19387`) its first
13 patches, and `l2r-base5` (head `c4a5df4b`, tree `402845d1`) its first
8 (before the C++ unit-test fixes in 02-b and 10-a).

Before the move to `00906e38` (2026-10-25), `l2r-base5` was upstream
`ea240b19` plus the same 8 patches (head `e1680f65`, tree `734cf027`).
Upstream `00906e38` (#804) only moves the commit of mlir-rcgmp that
Reussir's build fetches: no entry and no patch changed
([history](#history-the-move-to-00906e38-2026-10-25)).

Until the move to `ea240b19` (2026-10-25), `l2r-base5` was upstream
`0378b744` (2026-10-24) plus 9 patches (head `6bf9be85`, tree
`cb4c6d48`). Upstream `ea240b19` is
our pull request #758, which has the change of patch 05-a. The move to
`ea240b19` (2026-10-25) dropped 05-a, deleted entry 5 and retired its
number; the other 8 patches apply with no conflict, and in their files
only the commit ids and the patch counts changed
([history](#history-the-move-to-ea240b19-2026-10-25)).

The base before `0378b744` was `./reussir`'s branch `l2r-base3` (head
`4c490260`): upstream `7954a367` (2026-10-19) plus the same 9 patches.
They applied to `0378b744` with no conflict; in the patch files only the
line numbers and blob ids changed. The move to `0378b744` (2026-10-24)
fixed no entry and changed no number
([history](#history-the-move-to-0378b744-2026-10-24)).

Before `l2r-base3`, the base was `./reussir`'s branch `l2r-base2` (head
`b2e4a47e`): upstream `943f2195` plus 35 patches. Those 35 patch files,
and the entries this directory had before 2026-10-19, are in git history
and in that branch. On 2026-10-19 every entry that `7954a367` fixes was
deleted and the rest were renumbered
([history](#history-the-renumbering-of-2026-10-19)). Old entry 31,
deleted at first, came back the same day as entry 16 (upstream fixes it
only in part).

## Names

- **Entry numbers** run from 1 to 29. Numbers 5, 9, 11 and 22 are
  retired (2026-10-25): upstream `ea240b19` fixed entry 5 in full; Phase
  2 made entries 9 and 11 obsolete (they were about the drop series'
  shared stack, which is gone); and number 22 named a local patch that
  was never published here (retcon destructors that share their suspend
  points, `./reussir`'s branch `l2r-mergesusp`, commit `a8f3fc70`), which
  entry 23 superseded: with 23-f no pipeline made retcon destructors
  (upstream has deleted them since). No
  other entry gets these numbers; the other entries keep theirs. Number
  19, reserved until Phase 2 for the patch for upstream issue #759, is
  that entry. Entry 25 (the texture cache's key) is new with the move to
  `36a55a0f`. The patch names 24-a, 24-b and 24-c of the maintainer's
  port (lean2rr's pull request #4) were not patches of entry 24: they
  are folded into 10-a, 07-a, 20-c and 20-d, and no patch has that
  number. Entries 26, 27 and 28 are the upstream bugs that the port
  found (2026-11-18). Entries 19, 23 and 24 are fixed upstream and
  marked "to delete"; when they are deleted, their numbers are retired
  too. Entry 29 (rrc opens the texture cache's store once for each
  texture) is from 2026-11-18. The next free number is 30. Patch letters are not used again either: 20-f was the
  pin patch, so the patch that was split from 20-a is 20-g. (Old number 37 was
  reserved for another track's patch, value records across the FFI
  boundary; that track takes the next free number.)
- **A patch file** is named `NN-x-slug.patch`. NN is the number of its
  entry. The letter x gives the order of the entry's patches (a, b, c,
  ...). The slug is a short description. Every patch belongs to exactly one
  entry. In the text, a patch is named by NN-x: 20-b is the second patch of
  issue 20.
- **Patch file contents** are `git format-patch` output of the commits of
  `l2r-base13-final`, against `36a55a0f`, as one series (each subject
  has its patch count, `[PATCH NN/12]`; 29-a's file has no count, as
  it was exported again after its test changed). A file's subject line is the
  subject of its commit, in upstream Reussir's style, `[scope]
  description` (`[ffi]`, `[bigint]`, `[rc]`, `[rrc]`, `[trmc]`,
  `[codegen]`, `[conversion]`); it has no entry number. The body of each message
  says what the patch does, why, which tests it has and what was
  measured. No message names lean2rr. The parked files are older:
  20-b and 23-a to 23-p are their files from `l2r-base12`'s
  series (`[PATCH NN/24]`, against `95d9a1c8`), whose subjects name step
  D's patches R1 to R3 and the entries; the parked 19-a is its file from
  `l2r-base7`'s series (`[PATCH 3/8]`). 20-f's file (its subject "rcgmp
  pin") is in git history (commit `af521c12`). The
  [history](#history-the-renumbering-of-2026-10-19) maps old numbers to
  new ones.
- Older text says "bug NN" for every entry, whatever its kind: read it as
  "issue NN". Text inside the entries that names an entry or patch deleted
  on 2026-10-19 says "old NN" with the upstream pull request that fixed it.
  Text that names entry 5 or patch 05-a (old 34, 34-a) records the time
  before 2026-10-25. The entry, its patch and its repro are in git
  history, with no change since commit `0f9e1b05`:
  `reussir-bugs/05-executable-textrel.md`,
  `reussir-bugs/patches/05-a-pic-by-default.patch` and
  `reussir-bugs/repros/bug05-executable-textrel.rr` (for example
  `git show 0f9e1b05:reussir-bugs/05-executable-textrel.md`).
  Text that names patches 02-a to 02-e or 09-a, entries 9 and 11, or the
  parked 11-a records the time before Phase 2 (2026-10-25). Their last
  files are in commit `419a74d4` (dev): `reussir-bugs/09-drain-end-hook.md`,
  `reussir-bugs/11-drop-run.md`, `reussir-bugs/patches/02-a-*.patch` to
  `02-e-*.patch`, `09-a-drain-end-hook.patch`,
  `parked/11-a-drop-run.patch` and `repros/bug02-unlink-provenance.rs`.
  Text that names patches 23-a to 23-p or 20-b as parts of
  the series, the branch `l2r-base12` or `./reussir` as the built
  checkout records the time before the move to `36a55a0f` (2026-11-17).
  Text that names the branch `l2r-base13-folded` (head `d7952d77`, 5
  patches) records the first series on `36a55a0f` (2026-11-17), on
  which the port's first gate ran.

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
  (frees in native Lean's order, handles that may be a number). Its patch
  is a feature.
- *issue (dependency)*: an error in a library that Reussir pins, not in
  Reussir's own code (15: mimalloc v2.2.4). lean2rr works around it
  outside Reussir; the change on Reussir's side is a newer version of the
  dependency.
- *sharp edge*: correct by a rule that Reussir documents, but a caller
  that breaks the rule gets a wrong program with no message (25: the
  texture cache's key). lean2rr's driver keeps the rule; there is no
  Reussir patch.

## Status

One row per entry, grouped by kind. Column *Patches*: the entry's patch
files in the series, or "none", or a parked patch
([parked patches](#parked-patches)). Column *Upstream*: what upstream
`36a55a0f` does about it. The port's two gates (2026-11-18) ran
`repros/run.sh` on pristine `36a55a0f` and on the patched base:
"reproduces" and "FIXED" in the column are their verdicts; the numbers
in the cells are the first gate's, and the final gate gave the same
verdicts ([latest recorded run](#latest-recorded-run)). The checks
of the earlier bases: on `7954a367` on 2026-10-19 (a repro run, or the
source read); on 2026-10-24 the code of each entry was compared with
`0378b744` ([history](#history-the-move-to-0378b744-2026-10-24)); the
upstream commits from there to `95d9a1c8` changed no code of an entry
but entry 20's ([history](#history-the-move-to-95d9a1c8-2026-10-26)).
The 247 upstream commits from `95d9a1c8` to `36a55a0f` replace the drop
lowering (entries 2, 19, 23, 24), add a borrow analysis, change the
texture cache (entry 25) and the reading of nullary tags on aarch64,
and brought the three bugs of entries 26 to 28
([history](#history-the-move-to-36a55a0f-2026-11-17)).

| # | Kind | Effect | Affects lean2rr output? | lean2rr workaround | Patches | Upstream |
|---|---|---|---|---|---|---|
| [12](12-nullable-as-ref.md) | bug | reussir-rt's `Nullable::as_ref` returns a reference to a local copy of the pointer word (dangling) | no: nothing calls it | - | none | unchanged at `36a55a0f`; the repro fails both tests on pristine upstream and on the patched base (the port's first gate, 2026-11-18) |
| [13](13-small-allocation-limit.md) | bug (32-bit targets) | constant-size boxes of 513 to 1024 bytes go to `mi_malloc_small`, whose limit is 512 bytes there | no: 64-bit targets only | - | none | unchanged at `36a55a0f` (`alloc.rs` read, 2026-11-17) |
| [14](14-polyffi-rc-substitution.md) | bug (hand-written MLIR only) | a polymorphic-FFI substitution given as an MLIR rc type becomes Rust's `Rc` without the record's glue | no | - | none | unchanged at `36a55a0f` (source read on 2026-11-18; there is no repro) |
| [16](16-driver-stack-address-limit.md) | bug (under `ulimit -v`) | rrc's 1 GiB driver stack (#686) counts against an address-space limit: under `ulimit -v` 1250000 or 1600000 rrc aborts where it compiled before | no: lean2rr sets no such limit | - | none (parked: [16-a](patches/parked/16-a-driver-stack-rlimit.patch)) | open: the 1 GiB stack is unchanged at `36a55a0f` (`main.rs` read, 2026-11-17); #686 is the old 31-a; no pull request planned |
| [26](26-trmc-observable-release.md) | bug | TRMC moves a self call before a release that runs a foreign cleanup hook or drops a closure: the cleanup runs before the recursion, where the source runs it after | not known to: one constructed Lean program gave native's output, and the patch changes no TRMC helper of 19 lean2rr programs | - | [26-a](patches/26-a-trmc-observable-release.patch) | open at `36a55a0f` (also on `l2r-base12`); not reported |
| [27](27-is-unique-tbi-immediate.md) | bug (aarch64 with TBI; low severity) | `core::object::is_unique` answers true for a nullary immediate after 2^32 - 1 retains of it | no: lean2rr does not call the intrinsic | - | [27-a](patches/27-a-is-unique-tbi-immediate.patch) | open at `36a55a0f`, new with #983; not reported |
| [28](28-sve-vector-storage.md) | bug (aarch64 with SVE: valid code rejected) | rrc runs MLIR's SVE storage pass on every function; the pass fails on some large functions without any vector, and rrc stops with `RunPass` and no diagnostic | yes on a host with SVE: the row oracle of `rows-check.sh` did not compile | none | [28-a](patches/28-a-sve-vector-storage-patterns.patch) | open at `36a55a0f`, new with #994; the direct cause is in MLIR; not reported |
| [19](19-retcon-direct-arms.md) | bug (rrc out of memory); fixed upstream, to delete | the drop expansion writes a retcon variant's direct arms out in place at every drop site, nested types included: code exponential in type nesting (#759) | no: `36a55a0f` has no retcon destructors (on `l2r-base9` to `l2r-base12`, 23-f turned them off; on Phase 2's first base, `l2r-base7`, rrc ran out of memory on `RtSyncSelect` without the patch) | - | none (parked, history: [19-a](patches/parked/19-a-retcon-direct-arms.patch); its target code is gone) | fixed: upstream deleted the retcon drop lowering (#872) and closed #759 on 2026-11-01. The repro prints FIXED on pristine `36a55a0f` and on the patched base (the port's first gate, 2026-11-18) |
| [24](24-locked-drop-token-leak.md) | bug (a leak, with TPDE's drop options); fixed upstream, to delete | with tail-recursive and retcon drops off, a lock-guarded cell's payload is released inside the critical section, and its box is never freed | no: rrc has no TPDE level | - | none (it was fixed inside 23-e, which left the series) | fixed at `36a55a0f`: upstream's drop expansion calls a locked-drop function on every path; the repro prints FIXED on pristine `36a55a0f` (the port's first gate, 2026-11-18; skipped on the patched build, which has no `reussir-opt`). Never reported |
| [3](03-value-record-dag.md) | cost (deliberate design) | the first acquire/drop expansion writes a `[value]` record's copy out in line, exponential for records shared in a DAG | no, lean2rr's `[value]` records are shallow | - | none | reproduces on `36a55a0f` (3.93x; the port's first gate, 2026-11-18) |
| [4](04-emit-mlir-size.md) | cost (debug output) | the `--emit mlir` dump is exponential in the nesting of records that share sub-records | no, builds unaffected | dump smaller programs | none | reproduces on `36a55a0f` (3.99x; the port's first gate, 2026-11-18) |
| [23](23-worklist-drops.md) | cost (memory and run time); fixed upstream, to delete | retcon destructors kept one coroutine frame per level of a value being freed: memory grew with the depth (85 to 622 bytes per level) | no longer: upstream's scoped worklists are entry 23's design. On `l2r-base7` it did (`RtClosureChainFree` 652 MB, native 102 MB). On `36a55a0f` lean2rr's deep-free tests keep their allocation bounds (the port's first gate, 2026-11-18) | none | none (parked, history: [23-a](patches/parked/23-a-drop-stack-runtime.patch) to [23-p](patches/parked/23-p-same-release-cells.patch), sixteen) | fixed: the series of 2026-11-01 (#872 to #914) took the design; #760 closed on 2026-11-01. The repro prints FIXED on pristine `36a55a0f` and on the patched base (0 KiB in all four shapes) |
| [29](29-texture-store-open.md) | cost (build time) | rrc opens and closes the store of its texture cache for every texture; each open syncs the store and reads the whole database (about 19 ms for each texture with a small store, about 53 ms with a 140 MB store) | yes: build time of every program | none in the driver (a store on a memory file system removes the sync cost) | [29-a](patches/29-a-polyffi-store-once.patch) | open at `36a55a0f`, new with #852; not reported |
| [1](01-phantom-reuse-donor.md) | missed optimization | token reuse picks decrements that never free | yes, speed | fields bound lazily (`lazy-fields`) | none (parked: [01-a](patches/parked/01-a-sink-bound-retains.patch)) | reproduces on `36a55a0f` (4.79x pristine, 4.71x patched; the port's first gate, 2026-11-18) |
| [6](06-trampoline-inline.md) | missed optimization | a texture's import trampoline has no inline attribute: at a cold call site a texture costing more than 45 stays a call | yes, speed (three reads at cold sites) | read textures kept small | none (parked: [06-a](patches/parked/06-a-inline-small-textures.patch), [06-b](patches/parked/06-b-inline-guards.patch)) | reproduces on `36a55a0f` (the port's first gate, 2026-11-18) |
| [17](17-padded-member-widening.md) | missed optimization | with `--no-pack-record-members`, a member padded by the next one's alignment is widened to an integer but stored at its own width (`store i1`): LLVM keeps the struct on the stack | yes, speed (generated tuples with a `bool` first) | every generated tuple (join points, `flatten-structs`) in decreasing alignment (`memberOrder`) | none | reproduces on `36a55a0f` (2 stack slots; the port's first gate, 2026-11-18); not reported |
| [18](18-tail-padding-return.md) | missed optimization | a `[value]` struct's tail padding is an explicit byte array in the LLVM struct (`{ i64, i1, [7 x i8] }`); each byte counts as a returned value, so on aarch64 a result with more than 8 values comes back in memory (`sret`) | yes, speed (Unionfind +16% instructions on dev b874c365) | the tuple of a `flatten-structs` result keeps narrow values in `u64` members and no unit member (`tupleMemberTy`) | none | reproduces on `36a55a0f` (2 stores through `x8`; the port's first gate, 2026-11-18); not reported |
| [21](21-value-record-member-retains.md) | missed optimization | inc/dec cancellation keeps the retain of an rcgmp integer member extracted from a `[value]` record or tuple, and the member's release in the record's drop, a pair it cancels for an rc member | yes: speed. On `36a55a0f` with the patch: executed instructions L12 -5.5%, L17 -6.6% (cachegrind, reduced sizes); optimized IR L12 -3.3%, L17 -1.8%, Z01c -9.5%. Wall time: pending the timing run | none | [21-a](patches/21-a-value-record-member-retains.patch) (reworked for this base: a smaller rule) | not upstream at `36a55a0f` (source read) |
| [8](08-alias-release-donor.md) | missed optimization | token reuse takes the release of a value an opaque call returned (an alias, never freed) as the donor | no longer | a field put back into a rebuilt node is boxed again | none | reproduces on `36a55a0f` (32,020 and 129,488 cells; the port's first gate, 2026-11-18) |
| [2](02-native-drop-order.md) | missing feature (partly fixed upstream) | drop glue does not free in native Lean's order in every case. Upstream's `backward` policy (the default, which lean2rr passes) frees a whole value last field first, as native `lean_dec`; a drop run that starts inside a free finishes before it returns | yes: the release order of resources. On `36a55a0f` three older documented differences are gone, and two new ones that the first gate showed are answered in lean2rr's emitter. Left: a matched value that Reussir consumes in its `match`, a value that Lean's reset/reuse resets, a value shared by two fields of one freed cell | leanrt keeps its pending releases on Reussir's drop scopes; a value whose constructor Lean knows is released field by field (`l2r_release_known_<type>`); a box's payload release joins the running free (`payloadJoins`) | none (02-a to 02-e left the series in Phase 2) | the stack depth is bounded (worklist drops); the order is a switch, `--drop-order forward\|backward`, default `backward`. Native Lean's exact rule is not a mode |
| [7](07-tagged-top-bits.md) | missing feature | the inline count increment of a `tagged` handle uses all 64 bits as the address | yes: the one-word `Box` needs it | none | [07-a](patches/07-a-tagged-top-bits.patch) | not upstream at `36a55a0f` (the maintainer's pull request #923 with it was closed unmerged on 2026-11-05); the repro prints FIXED on the patched base (the port's first gate, 2026-11-18) |
| [10](10-tagged-ffi-objects.md) | missing feature | an opaque FFI handle must be a pointer to a counted box: it cannot be an immediate. On `36a55a0f` 10-a makes "only `rc.inc` and `rc.dec` touch the count of a tagged handle" a rule of the dialect (one predicate, a verifier rule) and keeps upstream's new readers of a count away from tagged handles | yes: the box `LAny` needs it (and until D8 the one-word `Nat` and `Int`) | none | [10-a](patches/10-a-tagged-ffi-objects.patch) | not upstream at `36a55a0f` (#923 closed unmerged; lean2rr's `Nat` and `Int` are upstream's built-in integers, #776, since D8; the box still needs tagged handles) |
| [20](20-rcgmp-integration.md) | missing feature | Reussir's built-in `Nat` and `Int` (rcgmp) lack what lean2rr's `Nat` and `Int` on rcgmp need: intrinsics for Lean's division modes and the power-of-two remainder, retain and release glue that inlines into textures, a query for sharing, and a parse of big literals that is not cubic (the owned handle at polyffi type arguments, whose absence was a bug, is upstream) | yes: lean2rr's `Nat` and `Int` are Reussir's built-in integers (step D; the only representation since D8) | none | [20-a](patches/20-a-bigint-lean-division.patch), [20-g](patches/20-g-bigint-nat-nonnegative.patch), [20-c](patches/20-c-mpz-inline-glue.patch), [20-d](patches/20-d-mpz-is-shared.patch), [20-e](patches/20-e-hex-bigint-literals.patch); parked: [20-b](patches/parked/20-b-mpz-handle-more-tests.patch) (tests) | in part: 20-b's code as #824, #843 and #845, 20-f's pin as #844 (2026-10-26; the pin is `dee6c102` now). The rest is not upstream at `36a55a0f`; the maintainer asked that these patches stay on lean2rr's tree (2026-10-25) |
| [15](15-mimalloc-arena-purge.md) | issue (dependency: mimalloc v2.2.4) | mimalloc's delayed arena purges do not run | yes, peak memory | leanrt sets `arena_purge_mult` to 0 on v2.1.8 to v2.2.7 | none (a newer `libmimalloc-sys` parked) | unchanged (still 0.1.44 at `36a55a0f`; `Cargo.toml` read, 2026-11-17) |
| [25](25-texture-cache-key.md) | sharp edge (documented rule) | rrc's texture cache is keyed on the paths of rustc and of the library directories, not on their contents: after a library is rebuilt in place, rrc reuses texture bitcode made against the old library, with no message | not with lean2rr's driver; a build without the driver's rule gets a wrong program | `scripts/l2r.py` puts the runtime build's digest into the path of the rustc that it gives rrc, and keeps the cache in lean2rr's own directory (`L2R_POLYFFI_CACHE`); test `tests/runtime/texture-cache-check.sh` | none | by design (#852): library directories are fixed inputs, a changed library needs a new path; upstream's own tests hit it and changed the caller (#967). |

**Counts.** 25 entries (numbers 1 to 29; numbers 5, 9, 11 and 22 are
retired): 9 bugs (2 of them fixed upstream and to delete: 19, 24), 4
costs (1 fixed upstream and to delete: 23), 6 missed optimizations, 4
missing features, 1 dependency issue, 1 sharp edge. 8 entries have
patches in the series, 12 patch files in all (one each for 7, 10, 21,
26, 27, 28 and 29, five for entry 20): 3 bug fixes (26-a, 27-a, 28-a),
4 features (07-a, 10-a, 20-a, 20-d) and 5 optimizations (20-g, 20-c,
20-e, 21-a, 29-a). 22 parked patch files lie outside the series (01-a,
06-a, 06-b, 16-a, 19-a, 20-b and 23-a to 23-p).

Status words used in the entries' summaries:

- *worked around*: lean2rr avoids the construct or works around it.
- *patched*: a local patch fixes it, or for an issue that is not a bug,
  improves it.
- *does not affect lean2rr*: lean2rr never produces the triggering shape.
- *open*: lean2rr can hit it and has no fix or workaround.

## Applying the patches

[`patches/base`](patches/base) holds the upstream commit that the series
applies to (one line, the full id of `36a55a0f`).
[`patches/series`](patches/series) lists the patch files, one per line,
in the order to apply them. To make a patched Reussir, from the
repository root, with a clone of upstream Reussir at `./reussir`:

```sh
git -C reussir checkout -b l2r-current "$(cat reussir-bugs/patches/base)"
while read -r p; do
    git -C reussir am --keep-non-patch "$PWD/reussir-bugs/patches/$p" || break
done < reussir-bugs/patches/series
cmake --build reussir/build --target rrc reussir-rt
```

`--keep-non-patch` is necessary: the subjects start with `[ffi]` or
`[bigint]`, and plain `git am` removes a leading `[...]`. The result has
the tree `ccdf369d` (checked on 2026-11-18). The Reussir branch
`l2r-base13-final` (head `d62797ac`, tree `9066f3fc`), on which the
final gate ran, differs from it in one test file of 29-a only. `scripts/l2r.py` uses the checkout
at `./reussir` unless `L2R_REUSSIR` names another one, and expects the
build in `<checkout>/build`.

The series on `36a55a0f` (12 patches; the whole series is 100 files,
without `tests/` 55 files; the commit ids are those of
`l2r-base13-final`):

| # | Patch | Commit | Subject | Kind | Lines (all; without `tests/`) |
|---|---|---|---|---|---|
| 1 | [10-a](patches/10-a-tagged-ffi-objects.patch) | `169d8db5` | `[ffi] support tagged foreign handles` | feature | +742/-50; +283/-50 |
| 2 | [07-a](patches/07-a-tagged-top-bits.patch) | `854f2b27` | `[ffi] mask tag bits before accessing foreign reference counts` | feature | +74/-6; +34/-2 |
| 3 | [20-a](patches/20-a-bigint-lean-division.patch) | `0212e8f1` | `[bigint] expose Lean division modes and power-of-two remainder` | feature | +468/-4; +137/-4 |
| 4 | [20-g](patches/20-g-bigint-nat-nonnegative.patch) | `c9e433ea` | `[bigint] divide Nats as nonnegative integers` | optimization | +110/-24; +58/-22 |
| 5 | [20-c](patches/20-c-mpz-inline-glue.patch) | `00e367fb` | `[bigint] emit inlineable acquire and release glue for foreign handles` | optimization | +343/-50; +135/-50 |
| 6 | [20-d](patches/20-d-mpz-is-shared.patch) | `d5a9f21b` | `[bigint] expose foreign handle sharing through generated glue` | feature | +240/-7; +114/-6 |
| 7 | [20-e](patches/20-e-hex-bigint-literals.patch) | `5baeed3b` | `[bigint] pass integer constants and match keys to MLIR in hexadecimal` | optimization (build time) | +142/-17; +75/-17 |
| 8 | [21-a](patches/21-a-value-record-member-retains.patch) | `3db9b817` | `[rc] cancel rcgmp retains of by-value record members against the record's drop` | optimization | +418/-2; +16/-2 |
| 9 | [29-a](patches/29-a-polyffi-store-once.patch) | `2b9d8ca0` (the file has the test of `1c867489`) | `[rrc] open the polyffi cache store once per module` | optimization (build time) | +53/-9; +35/-8 |
| 10 | [26-a](patches/26-a-trmc-observable-release.patch) | `25c44d22` | `[trmc] keep a self call in place across a release with an observable cleanup` | bug fix | +283/-13; +83/-13 |
| 11 | [27-a](patches/27-a-is-unique-tbi-immediate.patch) | `6e072b9b` | `[codegen] answer false to a uniqueness test of an immediate under TBI` | bug fix | +44/-2; +29/-2 |
| 12 | [28-a](patches/28-a-sve-vector-storage-patterns.patch) | `d62797ac` | `[conversion] legalize the storage of scalable vectors with the patterns alone` | bug fix | +155/-3; +102/-2 |

Order and dependencies:

- 07-a needs 10-a (the tagged handles whose increment it masks).
- 20-a, 20-g, 20-c and 20-d come after them, in that order. 20-g
  changes the divisions that 20-a adds and upstream's own; 20-c and
  20-d change upstream's `Mpz` (#824), and 20-d adds a function to
  20-c's glue.
- 20-e, 21-a and 29-a change no file near another patch's hunks; each
  applies with no conflict. 29-a touches three files that no other
  patch touches, and it applies to a clean `36a55a0f` alone.
- **The order has a reason: our own patches first, the three fixes of
  upstream bugs last.** Patches 1 to 9 are what lean2rr needs or gains
  (features and optimizations). 26-a, 27-a and 28-a are fixes of bugs
  that are upstream's own. They are independent of the rest and of
  each other: they apply to a clean `36a55a0f`, each alone and all
  three together (checked by `git am`). So the maintainer can take the
  last three without the Lean-specific patches, and a reader of the
  series sees where our part ends.
- Built alone: 10-a and 20-a; 20-g, 20-c and 20-d were each the head
  when they were built and tested. 07-a alone was only read.

### What each patch buys, and how it was measured

Every compiler change of the port has a measured claim (owner,
2026-11-17). The measurements are counts of instructions, calls and
bytes, and compile times of rrc; **none is a wall time of a lean2rr
program: those are pending the timing run.** All on aarch64. Each
entry has the details and what was not measured.

| Patch | What it buys | Measured claim | Where measured |
|---|---|---|---|
| 10-a | handles that can be immediates (the box `LAny`) | code without tagged types does not change: LLVM IR of 7 programs at two levels, pristine against patched, 0 differing lines. A tagged retain or release costs a test and a branch | pristine `36a55a0f` against the first series; the refinement against the first series on 8 lean2rr programs: identical IR |
| 07-a | foreign data in the top 16 bits of a tagged pointer | one AND on the retain of a boxed tagged handle; nothing for immediates and untagged objects (the same 7 programs) | as 10-a |
| 20-a | Lean's division modes and the power-of-two remainder as intrinsics | a `Nat` division in Lean's mode: 11 instructions on the immediate path and 24 in all, against 16 and 74 for `if b == 0 { 0 } else { a / b }`. No existing code changes (8 upstream units byte-identical after it) | assembly of small functions at `-O aggressive`; upstream's benchmark units |
| 20-g | unsigned division of `Nat` immediates | the composed `Nat` division: 23 to 16 instructions on the immediate path, 81 to 74 in all (`sdiv` to `udiv`); `divsi_lean` at `Nat` 15 to 11 | the compiler at 20-a against the compiler at 20-g |
| 20-c | clones and drops of `Nat` in Rust containers without a call | 100 copy-on-write copies of a 1000-element `Vec<Nat>`: 100,000 retain calls and 101,000 release calls to 0 and 0; object text 4215 to 4779 bytes (+13%) | pristine `36a55a0f` against the series, calls counted with `--wrap` |
| 20-d | the sharing query for `dbgTraceIfShared` | none (a feature for a debug primitive); one small function more in every unit with integers | - |
| 20-e | long integer literals compile | rrc on one literal of 20,000 digits: 8.17 s to 0.07 s; 40,000 digits: 74.57 s to 0.18 s; 100,000 digits: about 19 min (by the cube law) to 0.85 s. Objects byte-identical | one rrc process, user seconds, the first series without and with the patch |
| 21-a | fewer retains and releases of integers in value records | executed instructions (cachegrind, reduced sizes): L12 -5.5%, L17 -6.6%. Optimized IR: L12 -3.3%, L17 -1.8%, Z01c -9.5%; `.text` -4.3%, -2.8%, -12.2% | the same `.rr` through the first series without and with the patch |
| 29-a | the texture store is opened once for a module, not once for each texture | a warm rrc build of a program with 124 textures: 5.05 s to 3.16 s with a 1 MB store, 10.21 s to 3.09 s with a 140 MB store (wall, median of 3); two builds at once on the 140 MB store: 15.48 s to 3.49 s each; fsync 744 to 129. The reviewer measured the 140 MB rows again (10.13 s to 3.25 s). Generated code: byte-identical objects | the series without and with the patch, one rrc process on a shared machine (load 2 to 13); build time only |
| 26-a | a foreign cleanup runs after the recursion, as in the source | the repro: 0 open handles at the leaf to 3. Cost: no TRMC helper lost (18 of 18 helpers, 114 of 114 helper calls on upstream's benchmark, core and std; 7 of 7 and 40 of 40 on 19 lean2rr programs; lowered MLIR byte-identical) | pristine `36a55a0f` against the fix |
| 27-a | a right answer of `is_unique` for an immediate | the repro: 1 to 0 after 2^32 - 1 retains. Cost: none for a program without such a call (33 upstream units and 19 lean2rr programs byte-identical) | pristine `36a55a0f` against the fix |
| 28-a | large functions compile on a host with SVE | `rows-check.sh`: a build failure to `every row agrees`. Generated code: 33 upstream units byte-identical; 72 files of vector tests identical (2 of them after the random names of Rust modules are made equal) | pristine `36a55a0f` against the fix; the row oracle on the final series |

The whole series on other code: on upstream's benchmark suite with core
and std (33 units, lowered MLIR), 25 units are byte-identical to
pristine upstream; the other 8 (core, std and six integer programs)
differ by the three glue functions of 20-c and 20-d and by 20-g's `Nat`
divisions (6 functions). On 14 lean2rr programs of the runtime suite,
the series before 29-a against the first series: every difference is
21-a's, and each is a net removal of instructions. 29-a changes no
generated code (byte-identical objects of three lean2rr programs).

What lean2rr needs: `scripts/l2r.py` stops with an error when the
Reussir checkout lacks one of these texts (`REQUIRED_REUSSIR_PATCHES`,
`RCGMP_REUSSIR_PATCHES`):

- `join_or_run_step` and `defer_until_scope_exit` in
  `crates/reussir-rt/src/drop_stack.rs`. These are upstream code, not
  patches: they refuse a base from before upstream's scoped worklists
  (`l2r-base12` and older). leanrt's pending work is built on them and
  does not compile without them.
- 10-a: `isTaggedFFIObject(` in
  `lib/Conversion/AcquireDropExpansion/WorklistDrop.cpp`. The prelude
  declares the box `LAny` `tagged`, and rrc refuses the attribute
  without 10-a. The checked text is the patch's rule in the worklist
  drops: without it a build succeeds and a free reads an immediate as
  the address of a count.
- 07-a: `taggedBoxAddress` in `BasicOpsLowering.cpp`.
- 20-c: `__reussir_rcgmp_ffi_acquire` in `crates/reussir-rt/src/rcgmp.rs`.
  Without 20-c the programs would be correct but slower; the check is
  there because 20-d needs it.
- 20-d: `pub fn is_shared` in the same file. leanrt calls it.
- 20-a: `divsi_lean` in `library/core/src/intrinsic/bigint.rr`, and
  upstream's `pub struct Mpz` (`check_rcgmp`; lean2rr's `Nat` and `Int`
  are Reussir's built-in integers, the only representation since D8,
  2026-10-26).

- 26-a: `runsObservableCleanup` in
  `lib/Transformation/TRMCRecursionAnalysis/TRMCRecursionAnalysis.cpp`.
  Without it a build succeeds, and a release that runs foreign code can
  run before a recursion where the source has it after: a wrong release
  order with no message.
- 28-a: `createReussirLegalizeVectorStoragePass` in `lib/CAPI/Passes.cpp`.
  Without it rrc on an aarch64 host with SVE fails on a large function
  with `lowering pipeline failed: RunPass`. The check is made on every
  host.

The driver checks none of 20-g, 20-e, 21-a, 29-a and 27-a: without one
of them, lean2rr's programs build and give the same results (20-g and
21-a are optimizations, 20-e and 29-a build-time ones, and lean2rr's
programs do not call the intrinsic of entry 27).

So plain upstream `36a55a0f` fails at the 10-a check, and `l2r-base12`
at the first one (both checked on 2026-11-17). The driver does not check
the mlir-rcgmp pin. It passes `--drop-order backward` (upstream's
default, written out so that a change of the default cannot move
lean2rr's release order) and `--relocation-mode pic`, the workaround for
entry 5 (retired): since `ea240b19` this is rrc's default for
executables, so the flag is redundant but harmless. It also gives rrc a
texture cache of its own ([entry 25](25-texture-cache-key.md)). The
maintainer's series on `44abd17c` is refused too: it has the worklist
rule at one place and under no name.

**Adding a patch.** Name the file after its entry: `NN-x-slug.patch`, with
the next free letter of the entry (a new problem gets the next free entry
number, 30). Put it in `patches/` and add its name as the last line of
`patches/series`. Write the *Patch* and *Upstream note* sections of the
entry's file, and update the entry's row in the status table. Add a row to
the [review table](#review) when its review is done. A fix of one of our
own patches is folded into that patch (the series is made again), not
added as a new patch. Follow upstream Reussir's rules for patches (its
`AGENTS.md`): a `[scope] description` subject, a body that says what and
why, clang-format and rustfmt. Every patch needs a measured claim, in
its message and in its entry. A message does not name lean2rr.

### The series of the earlier bases (history)

Checked on 2026-10-26 (`git am` in a throwaway worktree): the series on
`95d9a1c8` gives tree `af82b837`, the tree of `./reussir`'s
`l2r-base12` (`c1170ff9`). The series before, on `00906e38`, gave
`l2r-base11`'s tree, `eb79e76e` (`a39e59b0`, with 20-f and the whole
20-b); without 20-f it gave `l2r-base10`'s tree,
`707daa79` (`0bea9c7d`); without 23-n to 23-p too it gave
`l2r-base9-shared`'s tree, `8b8dd1cb` (`6111586c`, 2026-10-25), and
without 23-k to 23-m too `l2r-base9`'s, `8c53abcf` (`fc9c1d20`). Phase
2's first base, `l2r-base7` (upstream `00906e38` plus 10-a, 07-a, 19-a
and entry 20's five; head `bfe3d32d`, tree `eeab2856`), never became
lean2rr's published base; `l2r-base11` was it without 19-a, with 21-a,
entry 23's patches and 20-f, and `l2r-base12` is that on `95d9a1c8`
without 20-f and with 20-b reduced to tests. Before Phase 2, the
series of 14 gave tree `10b34f74` (`l2r-base8`, head `8e9a6293`), and
before 21-a the series of 13 tree `b3b19387` (`l2r-stepd`,
`e3b96e03`). Before step D's patches, the series of 8 patches gave
`l2r-base5` on `00906e38` (tree `402845d1`, head `c4a5df4b`), and
before that `l2r-base5` was made the same way from the same series on
`ea240b19` (tree `734cf027`, head `e1680f65`), and before that from the
series of 9 patches (with 05-a) on `0378b744` (tree `cb4c6d48`, head
`6bf9be85`); `l2r-base3` from that series on `7954a367` (tree
`cc4a28d9`), and `l2r-base2` from the old series on `943f2195` (git
history).

On `l2r-base12` (history) the order was: 10-a, 07-a, 20-a to 20-e, 21-a,
then 23-a to 23-p. 20-e changed code next to 20-a's
(`lower/expr/bigint.rs`, the backend's `rcgmp.rs`); 21-a changed no file
of another patch; 23-b lowered to 23-a's runtime functions, 23-d used
23-b's ops and 23-c's helper, 23-e to 23-j changed 23-d's glue
(`WorklistDrop.cpp`), 23-f switched the pipelines, 23-k to 23-n and 23-p
changed only 23-a's runtime stack (`drop_stack.rs`), and 23-o 23-b's
lowering. `scripts/l2r.py` then required 23-f, 23-k, 23-m, 23-n, 23-o
and 07-a, so `l2r-base9` and `l2r-base9-shared` failed its check too
(`RtAltTreeFree`'s bounds are native's, which needed the links). With
the older mlir-rcgmp pin `ca288d5e` (before 20-f and #844), code
dominated by big quotients ran slower: L11 40.10G instructions instead
of 33.50G.

### Building Reussir

Since `0378b744`, Reussir builds its rcgmp integration by default
(`REUSSIR_ENABLE_RCGMP=ON`): the built-in `Nat` and `Int` on rcgmp,
Reussir's arbitrary-precision integers (upstream #770 to #803).
lean2rr's builds keep the default (the combined gate of 2026-10-24 used
it). The build then needs these, in addition to LLVM, MLIR and Clang 23:

- GMP 6.2 or later: `gmp.h` and `libgmp` where CMake finds them (on
  Ubuntu, `libgmp-dev`). For GMP in another prefix, add the prefix to
  `CMAKE_PREFIX_PATH`. Without GMP, configuration stops with an error
  (`cmake/RCGMP.cmake`).
- A CMake that knows `cxx_std_26` for Clang: rcgmp's C++ runtime asks
  for it. CMake 3.28 (Ubuntu 24.04's) does not know it; CMake 4.4.4
  works (for example from `pip install cmake` in a Python virtual
  environment).
- The libstdc++ 14 headers: rcgmp's runtime uses `std::add_sat`. Clang
  uses the headers of the newest GCC installation that it finds; on
  Ubuntu 24.04, install `libstdc++-14-dev`.
- The rcgmp sources: at the first configuration, CMake fetches
  mlir-rcgmp from GitHub into the build directory's `_deps`, at the
  commit that `cmake/RCGMP.cmake` pins (`GIT_TAG`; `dee6c102` at
  `36a55a0f`, which has mlir-rcgmp #49 to #53; before: `cc73b218` since
  #844, `5aeb834d`, and with 20-f before that; `ca288d5e` since
  `00906e38`; `c2a68d81` before). An offline
  build needs them there first (or `FETCHCONTENT_SOURCE_DIR_RCGMP` set
  to a checkout of that commit).

After a change of the C++ headers (for example after you install
`libstdc++-14-dev`), delete the build directory and configure again. The
C++ module files (`.pcm`) that the old headers made stay in the build
directory, and the build then fails with "ambiguous deduction for
std::span".

The port's builds of `36a55a0f` used CMake 4.4.4, Clang, LLVM and MLIR
23.1.2, Rust `nightly-2026-08-31` (upstream's `rust-toolchain.toml`) and
the targets `rrc` and `reussir-rt`. Three things to know on this base:

- The archive of the rcgmp runtime is `build/lib/libRCGMPRuntime.a`; the
  `reussir-rt` target copies it to `build/target-rt/release/deps`, where
  `scripts/l2r.py` finds it.
- `reussir-opt` (for the repro of entry 24) and Reussir's lit tests need
  a build with the tests on (`REUSSIR_ENABLE_TESTS=ON`), which needs GTest
  and lit.
- rrc keeps compiled textures in a cache for each user
  ([entry 25](25-texture-cache-key.md)). A run of rrc by hand after a
  rebuild of reussir-rt needs a new cache directory (`XDG_CACHE_HOME`);
  builds through `scripts/l2r.py` need nothing.

### Parked patches

A parked patch was made and reviewed, but lean2rr's builds do not apply
it. Its file is in [`patches/parked/`](patches/parked/), outside
[`patches/series`](patches/series) and the counts above; its entry says
why it is parked and describes the patch. Two groups:

- Parked by the owner's decision (the first four rows).
- Out of the series since the move to `36a55a0f` (the last two rows).
  These files are the `l2r-base12` versions, against `95d9a1c8`: they
  are kept as they were reviewed.

20-e and 21-a were parked from 2026-11-17 to 2026-11-18, while they
were measured on the new base; they are in the series again (21-a
reworked), and their old-base files left `parked/`.

| Patch | Entry | Kind | Parked | Why | On `36a55a0f` |
|---|---|---|---|---|---|
| [01-a](patches/parked/01-a-sink-bound-retains.patch) | [1](01-phantom-reuse-donor.md) | optimization | 2026-10-07 | a missed optimization; lean2rr's `lazy-fields` covers it | not checked (it did not apply to `95d9a1c8`) |
| [06-a](patches/parked/06-a-inline-small-textures.patch), [06-b](patches/parked/06-b-inline-guards.patch) (review fixes) | [6](06-trampoline-inline.md) | optimization | 2026-10-07 | the gain is too small for a local Reussir patch | not checked (they did not apply to `95d9a1c8`) |
| [16-a](patches/parked/16-a-driver-stack-rlimit.patch) | [16](16-driver-stack-address-limit.md) | bug fix | 2026-10-19 | lean2rr does not reach the bug | not checked (it applied to `95d9a1c8` and `l2r-base12`) |
| [19-a](patches/parked/19-a-retcon-direct-arms.patch) | [19](19-retcon-direct-arms.md) | bug fix | 2026-10-25 | lean2rr did not reach the bug since 23-f | history, to delete with entry 19: upstream deleted the code that it changes (#872) |
| [20-b](patches/parked/20-b-mpz-handle-more-tests.patch) | [20](20-rcgmp-integration.md) | tests | 2026-11-17 (out of the maintainer's series since 2026-11-05); decided on 2026-11-18: it stays parked | tests only, so no measured claim is possible; it found nothing on the new base; it edits three upstream test files | applies with no conflict, and its tests pass there (7 of 7 `frontend/bigint_ffi*` lit tests and the unit test) |
| [23-a](patches/parked/23-a-drop-stack-runtime.patch) to [23-p](patches/parked/23-p-same-release-cells.patch) | [23](23-worklist-drops.md) | optimizations, features, tests | 2026-11-17 | upstream has the design (2026-11-01) | history, to delete with entry 23: not to be applied |

The parked files 01-a, 06-a and 06-b are against the stacks they were
made on (`ef922049` plus earlier patches of the old series); 16-a is
against `7954a367`, 19-a against `l2r-base7` (`00906e38` plus 10-a and
07-a); 20-b and 23-a to 23-p against `95d9a1c8` with the
patches before them in `l2r-base12`'s series. The moved version of 20-b
is on a Reussir branch of the port (`m1-20b`); it replaces the parked
file if the patch comes back.
For 01-a, 06-a, 06-b, 16-a and 19-a the last check was on 2026-10-26
(`git apply --check` on `95d9a1c8` and `l2r-base12`; the same results on
`00906e38`, `0378b744`, `ea240b19` and the bases between). The parked
11-a was deleted with entry 11 in Phase 2 (it needed 02-c and 09-a). To
park a patch of the series, move its file to `patches/parked/`, delete
its line from `patches/series`, make the Reussir stack again from the
series, and update the entry, its row and the counts.

## Running the repros

[`repros/`](repros/) has one repro per entry that can show its issue with
Reussir alone: a plain Reussir program (`bugNN-name.rr`), a Lean program
built through lean2rr (`bugNN-name.lean`), a small generator
(`bugNN-name.py`) where the program must be large, a Rust test of
Reussir's runtime sources (`bug12-nullable-as-ref.rs`), a Reussir
program with a C driver (`bug23-deep-free.rr` and `.c`, linked with
`cc`), or MLIR for `reussir-opt` (`bug24-locked-drop-token.mlir`; a
build without the tests has no `reussir-opt`, and `run.sh` then prints
`SKIPPED`). `bug01b-call-before-branch.rr` is a variant used in issue
1's entry. Entry 2's repros show the part of it that upstream fixed (a
bounded stack depth), as checks of that part. Entries 10, 20 and 21
have no repro in `repros/`; entry 25's repro is described in its file
(it needs a Rust library built twice). Entries 26 and 27 have a Reussir
program with a C driver, and entry 28 a generator of plain MLIR for
`mlir-opt` (`bug28-sve-storage-chain.py`; no `.rr` program reaches that
bug without lean2rr). `bug02-nested-run-order.rr` shows a rule of
upstream's drop scopes that is not a bug (entry 2); `run.sh` runs it
and reports whether the behaviour that the entry documents was seen
(it prints `1 2`, then `2 1`, on pristine `36a55a0f` and on the
series). 10 and 20 are missing features that show only through a
host that uses them, and their patches carry their own tests (20-b's
tests showed its bug: they failed with `l2r-base5`; those tests are
upstream's now, #843 and #845). 21's patch has a
lit test that shows the missed optimization (the test fails without the
patch), and its entry gives the program and the measures. Entries 13 to
16 have none either: 13 needs a 32-bit target, 14 MLIR written by hand,
15 is shown by lean2rr's runtime test `RtArenaPurge` (its peak memory,
through `tests/runtime/alloc-check.sh`), and 16 by upstream's own test
under a `ulimit -v` (its entry gives the command). Each repro file starts
with what it shows and the expected output.

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

**On `36a55a0f`** (the port's final gate, 2026-11-18): `run.sh` of
lean2rr `8d032fdb` ran without an error on pristine upstream `36a55a0f`
and on the final series (Reussir `d62797ac`, 12 patches).

| Entry | Pristine `36a55a0f` | Final series | Verdict |
|---|---|---|---|
| 1 | REPRODUCES (4.98x) | REPRODUCES (5.08x) | still there, no patch |
| 2, plain repros (list, snoc list, left spine, `Nullable` chain) | FIXED (4 lines) | FIXED (4 lines) | the bounded depth is upstream's |
| 2, Lean repro (40,000,000 cells) | OTHER: the driver refuses pristine upstream (no 20-a) | FIXED (2 lines) | works on the series |
| 3 | REPRODUCES (3.93x) | REPRODUCES (3.93x) | still there, no patch |
| 4 | REPRODUCES (3.99x) | REPRODUCES (3.99x) | still there, no patch |
| 6 | REPRODUCES | REPRODUCES | still there, no patch |
| 7 | OTHER: rrc rejects the `tagged` attribute (no 10-a) | FIXED (prints 143) | fixed by 10-a and 07-a |
| 8 | REPRODUCES | REPRODUCES | still there, no patch |
| 12 | REPRODUCES (2 of 2 tests fail) | REPRODUCES | still there, no patch |
| 17 | REPRODUCES | REPRODUCES | still there, no patch |
| 18 | REPRODUCES | REPRODUCES | still there, no patch |
| 19 | FIXED (1.28x) | FIXED (1.28x) | fixed upstream |
| 23 | FIXED (0 KiB in all 4 shapes) | FIXED (172, 192, 192 and 192 KiB; the limit is 16 MiB) | fixed upstream; the series' build grows by less than 200 KiB where pristine grows by 0 |
| 24 | FIXED (1 `token.free`) | FIXED (1 `token.free`) | fixed upstream; checked on the patched build too |
| 26 | REPRODUCES (0 handles open at the leaf, the source keeps 3) | FIXED (3, control 3) | fixed by 26-a |
| 27 | REPRODUCES (true after 2^32 - 1 retains) | FIXED (false) | fixed by 27-a |
| 28 | REPRODUCES (MLIR's pass fails a chain of 13 blocks, exit 1, no message) | FIXED (the pipeline's pass succeeds; MLIR's own pass still fails) | fixed by 28-a; `rows-check.sh` confirms it on the real program |

No verdict is against its entry. The first gate of the port (the first
series, 5 patches, Reussir `d7952d77`) gave the same verdicts for
entries 1 to 24 (entry 1: 4.79x and 4.71x; entry 23: 0 KiB on the
patched base; entry 24 skipped on the patched build).
`repros/bug02-nested-run-order.rr` was not yet run by `run.sh` at the
gate; `run.sh` runs it since then. Entries 25
and 29 have no repro in `run.sh` (each entry gives its runs).

`run.sh` gives each run a new, empty texture cache in its work
directory (`XDG_CACHE_HOME`, `XDG_CONFIG_HOME`; the Lean repros build
with `L2R_POLYFFI_CACHE` empty) and names the drop order as the driver
does. rrc at `36a55a0f` does not read the old `REUSSIR_FFI_CACHE_DIR`,
and its cache cannot be turned off
([entry 25](25-texture-cache-key.md)). So the rrc times that the
script measures (entries 3, 4, 19) are with an empty cache, as before.

The runs on the earlier bases (history):

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
Lean repro needs leanrt, which does not build there. The repros were not
run again on `l2r-base5`, neither on `0378b744` (2026-10-24) nor on
`ea240b19` or `00906e38` (2026-10-25), nor on `l2r-stepd` or with
21-a; lean2rr's
combined gate passed on `l2r-base5` ([review](#review)).

On `l2r-base9` (2026-10-25, its code built with the tests on, for
`reussir-opt`) the new repros ran: issues 19, 23 and 24 FIXED (19:
`--emit mlir-llvm` N = 3 59 KB, N = 4 69 KB, 1.16x, since rrc makes no
retcon destructors; 23: peak growth 2052, 2052, 0 and 0 KiB; 24: one
`token.free`, in the locked-drop function); on upstream `00906e38` all
three REPRODUCE (19: 1167 KB and 4599 KB, 3.93x; 23: 83972, 83972,
608264 and 86020 KiB; 24: no `token.free`). On `l2r-base9-shared`
(23-k to 23-m change only Reussir's runtime) issues 19 and 23 printed
FIXED again (23: no growth for any of the four values); 24 was not run
there (its build has no `reussir-opt`; the code it tests is the same).
On `l2r-base10` (2026-10-26) issues 19, 23 and 24 printed FIXED (19:
59 KB and 69 KB, 1.16x; 23: no growth for any of the four values; 24 on
a build of the same commit with `reussir-opt`: one `token.free`). On Phase 2's first base `l2r-base7`, issue 19's repro printed
FIXED with 19-a (322 KB and 457 KB, 1.41x).

## Policy

- Every Reussir problem lean2rr meets is documented here, with a repro,
  until upstream fixes it. When upstream fixes an entry fully, the entry,
  its patches and its repros are deleted (they stay in git history), and
  its number is retired: the other entries keep their numbers (since
  2026-10-25, entry 5; on 2026-10-19 the remaining entries were
  renumbered). An entry that a change on lean2rr's side makes obsolete
  (no Reussir problem left for lean2rr: entries 9 and 11 in Phase 2) is
  deleted and its number retired the same way. An entry upstream fixes
  in part keeps only the part that remains, with a reduced patch.
- A real Reussir bug (verified reproducible erroneous behaviour) gets a
  small local patch, reviewed adversarially, even if lean2rr never
  triggers it or works around it.
- Only bug fixes and major items stay in the series (owner, 2026-10-07):
  the bug fixes (26-a, 27-a and 28-a; the earlier ones are upstream:
  05-a as #758, 20-b's fix as #824 and #843, and upstream's own drop
  lowering has what 23-e fixed), the features lean2rr needs (07-a,
  10-a, 20-a, 20-d) and optimizations with a measured gain (20-g, 20-c,
  20-e, 21-a). A fix of a bug that lean2rr does not reach is
  parked (16-a). On `l2r-base12` the series also had entry
  23's worklist drops (652 MB to 68 MB on `RtClosureChainFree`), which
  upstream has now.
- Every bug found in upstream Reussir during the port gets a patch that
  is kept in this series, also when lean2rr does not reach the bug
  (owner, 2026-11-17: entries 26, 27, 28). Each of these fixes applies
  to plain upstream alone.
- Every compiler change of the port to `36a55a0f` comes with a measured
  claim (owner, 2026-11-17), stated in the patch's message and in its
  entry, with what was and was not measured
  ([the table](#what-each-patch-buys-and-how-it-was-measured)). For
  this reason 20-e and 21-a were out of the series for one day, and
  20-b (tests only) stays parked.
- A Reussir change is the last resort (owner): where lean2rr's runtime
  can do the work itself, it does, and the local patch goes (Phase 2:
  leanrt's own stack of pending releases replaced 02-a to 02-e and
  09-a). Entry 23 changed Reussir because the cost was in Reussir's own
  drop glue, which lean2rr's runtime does not run; upstream took that
  design on 2026-11-01, and leanrt keeps its pending work on upstream's
  drop scopes, with no second stack beside them.
- A patch that only buys a small run-time gain on a few programs is
  parked, not kept (01-a, 06-a with 06-b; 11-a until Phase 2). Costs
  whose removal would be a redesign (3, 4) and missed optimizations stay
  unpatched, with the reason in their file.
- Pull requests: after #758 (05-a, merged as `ea240b19`) none for the
  patches of this directory (owner, 2026-10-19). Since 2026-10-25 the
  owner's rule is: rcgmp-related Reussir fixes and optimizations may go
  upstream as pull requests of at most 300 changed lines each, one
  reviewable and actionable change per pull request; the other local
  patches stay in the series. 20-b went upstream so (#824, #843, #845),
  and so did 20-f's pin (#844). The maintainer then asked for no pull
  requests on Reussir's side for these changes ("Please make those
  patches sitting on your tree", 2026-10-25): entry 20's other patches
  and 21-a stay here.
- A local move of a dependency's pin (20-f, mlir-rcgmp, until #844)
  stands in for upstream's own: it is dropped when upstream Reussir moves
  its pin to that commit or a later one, as it did for mlir-rcgmp #48 in
  #804 and for 20-f's `cc73b218` in #844.
- Patches are local: lean2rr's work does not push them. The "Upstream
  note" at the end of a patched entry is text for an upstream report.
  Reussir's maintainer asked that Reussir-side changes for lean2rr be
  made here first, as patches on lean2rr's tree; he takes them from this
  directory himself (2026-10-25). So a patched entry must be readable on
  its own: what each patch does, why lean2rr needs it, its tests and its
  evidence (entries 20, 21, 23 and 24 are written so). The maintainer's
  own port (lean2rr's pull request #4, 2026-11-05) keeps "all
  Lean-specific compiler extensions" in this series.
- lean2rr's workarounds stay, so that lean2rr also works with an unpatched
  Reussir. The exceptions are the features lean2rr requires
  ([what lean2rr needs](#applying-the-patches)). The workarounds for
  entries that upstream `7954a367` fixed are listed in
  [`docs/implementation/reussir-workarounds/`](../docs/implementation/reussir-workarounds/README.md)
  as "removable after the move". lean2rr's builds use a later base
  (`36a55a0f`), so each can go, one change per workaround, with its test.

## Review

Each patch is reviewed adversarially: code review, differential fuzzing
against an independent reference evaluator, ASan builds (Miri for the
runtime patches), and lean2rr's runtime suite and corpus, in rounds
repeated until one finds nothing. The review notes are local notes,
outside this repository (column *Notes*: their names). The rows below
record the reviews on the earlier bases (history), but for the row of
the series on `36a55a0f`. The patches were
reviewed under their old names, on the old base (entry 20's patches
under their step D names, on `00906e38`; entry 23's on `l2r-base7`). The
rows of the patches that left with Phase 2 (02-a to 02-e, 09-a) are in
git history (commit `419a74d4`):

| Patch (old name) | Round | Notes | Result |
|---|---|---|---|
| 07-a (38-a) | review-anybox r1 | `review-anybox/r1` | no defect; the atomic case was added to the patch's test |
| 10-a (41-a) | mem-nat review, RV8 | `mem/nat/review/FINDINGS.txt`, `rv8/nat/FINDINGS.txt` | no defect (the optional hardening is in) |
| 20-a (R1) | step D review | `stepd-r12/review/r1`, `stepd-r12/review/r1b` | no bug in the final version |
| 20-b (R2) | step D review | `stepd-r12/review/r2` | no bug in the final version (its code upstream since #824 and #843; the series keeps its other tests) |
| 20-c (R2b) | step D review | `stepd-r12/review/r2b` | no bug in the final version |
| 20-d (R2c) | step D review | `stepd-r12/review/r2c` | no bug in the final version |
| 20-e (R3) | step D review | `stepd-r12/review/r3` | no bug in the final version |
| 21-a | independent review | `rccancel-review/` | sound; its three findings (test inputs, the crossed operations in the message with a negative test, the stop at `rcgmp.bridge.mpz.is_unique`) are in the patch |
| 23-a to 23-j | two adversarial rounds (runtime, IR and pipeline; glue, member kinds, release order and tests), then an independent re-review | `lifodrop-review/rt/NOTES.md`, `lifodrop-review/gen/NOTES.txt`, `lifodrop-review/gen/v2/` | round one: two order bugs (the tail call taken although a later member pushed; an anonymous recursive arm taken for a leaf), the TPDE token leak (entry 24), a flex box accepted by `rc.defer`, a defer outside a drain that waited for a later drain, a buffer leaked after the thread-exit guard, and documentation and test gaps: all fixed in the patches; re-review: the type predicates exponential on generated inputs (fixed: one reachability walk per query), nothing else; the fixes were checked with targeted lit tests and ASan |
| 23-k to 23-m | made and tested by the runtime side, then an adversarial review (2026-10-25) | `phase2/shared/` | its fixes are in the patches: a step is `extern "C"`, so a panicking step aborts instead of unwinding with the thread marked as draining; the nesting of end work requested inside the end function (one level per generation, as natively) and the entry costs of runs are documented; on the first version (`fbc2bba2`), leanrt's unit tests 101 of 101 (leanrt build) and 104 of 104 (rcgmp build) and the trace digests of 400 random order scenarios equal to those of leanrt's own stack |
| 23-n, 23-o | an adversarial review (2026-10-26) | `lifodrop-review/rt/link/` | no bug: every box 23-o routes to `defer_wide` has the claimed header on every target (i686 narrow, wasm32 right, big-endian safe); headers back before each release; the order with host cells, steps, runs, nested runs and end work in a model check with real boxes (3000 seeds x 3 natively, 40 x 3 under Miri, both borrow models); the 40-bit offset right at +-2^42. Its cleanups (the table zero-initialized, the linked flag in the count's top bit, two comments) are in 23-n |
| 23-p | short re-review pending; the review's model check, with a joined box allowed (count untouched, upper bits 0), passes (3000 x 3 natively, 40 x 3 under Miri) | `lifodrop/link/` | instructions per freed cell back near `l2r-base9-shared`'s (balanced tree 59.08 against 57.08, rose tree 54.55 against 52.77); `RtAltTreeFree` 45.7 MB kept |
| 10-a, 07-a on `36a55a0f` | independent review (2026-11-17), then a review of the refinement (2026-11-18) | `port13/reviews/RV1`, `RV6` | no hole in the rule; its findings are in the patch: one predicate and a verifier rule, the contract of the foreign type (a first form of the check, a niche test, was found wrong by the second review and replaced), an end-to-end array test. Code without tagged types: identical IR |
| 20-a, 20-g, 20-c, 20-d on `36a55a0f` | independent review (2026-11-17), then a review of the refinement (2026-11-18) | `port13/reviews/RV2`, `RV6` | no bug in the three patches (20-a's semantics: 23,860 checks, 0 failures). Findings in the patches: the three unused intrinsics removed, 20-g split off, the glue defined in every unit, hidden visibility by a module attribute. The second review found one regression of the refinement (a program with `Nat` only as a type argument inside a foreign body did not link); fixed by restoring the glue entry, with a test |
| 20-e, 21-a on `36a55a0f` | independent review (2026-11-18) | `port13/reviews/RV5` | 20-e approved as moved. 21-a approved with changes, which are in the patch: the scan rule is one operation (`ref.spilled`) instead of an effect rule, the `is_unique` stop is gone; the pair counts of the commit message are the review's |
| 26-a, 27-a, 28-a | independent review, two rounds for 26-a and 27-a, one for 28-a (2026-11-18) | `port13/reviews/RV4` | 26-a: round 1 found the fix incomplete (releases through `drop.run`) and too wide (records of integers); both fixed, round 2 approved. 27-a: approved. 28-a: approved with one change, which is in the patch (the check for a use that is left over) |
| 29-a | independent review, two rounds (2026-11-18) | `port13/reviews/RV3` (the two "Store opened once" sections) | round 1 (a handle in a function-local static): correct and the claim reproduced, but the handle must be owned by the caller; reworked. Round 2: accepted; the 140 MB rows measured again (10.13 s to 3.25 s). One recommended change to the new lit case, which is in the patch file |
| the final series (12 patches) | checks on the stack (2026-11-18), then lean2rr's final gate | `port13/research/I7`, `port13/gate54` | lit: 174 of 189 selected tests pass, 15 unsupported (13 sanitizer tests, 2 that need a build without rcgmp), 0 fail; `reussir-ut` 97 of 97; cargo tests of reussir-core (677), reussir-codegen (87), reussir-backend (29): 0 failed. Not run: the full lit suite, clang-tidy, the sanitizer tests; clang-format is not installed on the build machine |
| 19-a (parked) | issue #759's measurements (prototype "a+m2", on 7954a367); `l2r-base7` checks | `r759/RESULTS.md`, `reussir-move/base7/` | not reviewed adversarially; the prototype passed Reussir's 66 lit tests that touch drops; on `l2r-base7` lit 767 passed, 2 failed for want of the `not` tool, 125 unsupported; `reussir-ut` 82 of 82 |

The rebase onto `7954a367` (2026-10-19) is not reviewed yet: 10-a had two
conflicts (upstream added the `placement` and `launch` fields to
records), 02-a, 02-b and 02-d five small ones (listed in issue 2's file
in commit `419a74d4`), and 02-b needed one line
(the drain declaration in the shared symbol table). Tested: the repros
above and 13 targeted lean2rr runtime tests (issue 2's entry lists them).

The move to `0378b744` (2026-10-24) applied the same 9 commits with no
conflict (`git cherry-pick`), so their code is the same as on
`l2r-base3`. lean2rr's
combined gate passed on `l2r-base5` (gate19, dev `0810b9ec`): 658 of
660 runtime tests identical to native, 2 expected failures, all 15
checks, the classic corpus with the optional passes on, with all 23 off
and with `unread-fields`, and the raytracer.

The move to `ea240b19` (2026-10-25) dropped 05-a and applied the other 8
commits with no conflict, so their code is the same as on `0378b744`.
rrc on `e1680f65` behaves as on `6bf9be85`: upstream's condition for PIC,
`target.is_linked()`, is `Stage::Dynlib | Stage::Executable`, the same
as 05-a's `matches!`. The other differences between the two heads
(`git diff 6bf9be85 e1680f65`, 5 files) are comments, the CHANGELOG and
two codegen tests. lean2rr's last combined gates (2026-10-24 and
2026-10-25) ran on `6bf9be85`.

The move to `00906e38` (2026-10-25) applied the same 8 commits with no
conflict. The only difference between the heads `e1680f65` and
`c4a5df4b` is the `GIT_TAG` of mlir-rcgmp in `cmake/RCGMP.cmake`
(`git diff e1680f65 c4a5df4b`).

On `l2r-stepd` (2026-10-25), two of the 8 patches changed, for Reussir's
C++ unit tests (`reussir-ut`), which did not build with the tests on:
02-b updates upstream's `glue_symbols.cpp` (6 `func.func` operations, not
5: the non-atomic dtor's `__reussir_drop_drain` declaration), and 10-a
adds the two-parameter `FFIObjectType` builder that upstream's
`record_drop.cpp` uses. With both, 82 of 82 pass. The rest of the 8 is
unchanged (`git diff c4a5df4b 45566790`: these 2 files).

Phase 2 (`l2r-base9`, 2026-10-25) applied 10-a, 07-a, entry 20's five
patches and 21-a with no conflict and no change of code (in their patch
files only the commit ids, the patch counts and line offsets changed;
02-b's update of upstream's `glue_symbols.cpp` went with 02-b, and
without 02-b upstream's test is right as it is), then entry 23's first
ten. The stack of 10-a, 07-a and entry 20's five, made from
`l2r-base8`'s commits (dropping 02-a to 02-e and 09-a) and from
`l2r-base7`'s (dropping 19-a), gives one tree (`dbdd2dea`). Checks on
`l2r-base9`'s code (a build with the tests and the ASan runtime):
Reussir's lit tests 776 passed, 125 unsupported, 2 failed
(`frontend/kernel_launch_config_errors.rr` and
`kernel_launch_disabled.rr`: the test environment has no `not` tool);
`reussir-ut` 82 of 82; the repros of entries 19, 23 and 24 FIXED. rrc
compiles `RtSyncSelect` in 1.94 GB and `RtDepPolyRec` in 3.47 GB
without 19-a (entry 19). `l2r-base9-shared` adds 23-k to 23-m, which
the runtime side made for leanrt and which change only reussir-rt's
`drop_stack.rs` and its tests (reviewed, 2026-10-25). `l2r-base10` adds
23-n to 23-p (2026-10-26): the same 21 commits, then three; checks in
[issue 23](23-worklist-drops.md#tests).

## History: the move to 36a55a0f (2026-11-17)

Upstream Reussir moved from `95d9a1c8` (2026-10-26) to `36a55a0f`
(2026-11-17), 247 commits. `l2r-base12` (24 patches) became a stack of
12 patches (5 in its first series of 2026-11-17). The move had five
steps.

**1. Upstream's changes that matter to lean2rr.**

| Upstream | Change | Entries |
|---|---|---|
| #872 to #914 (2026-11-01) | the retcon drop lowering, its LLVM passes and `dtor_executor.rs` are deleted; drops of recursive records go through scoped worklists (`crates/reussir-rt/src/drop_stack.rs`): typed callbacks that return `StepStatus`, `join_or_run`, `join_or_run_step`, `defer_wide` (dead boxes linked through their headers), `defer_until_scope_exit` (work after the outermost scope) | 23 (the design is upstream), 19 (its code is gone), 24, 2 |
| #913 | `--drop-order forward\|backward`, default `backward` | 2 |
| #924, #928, #968 | no worklist entry for an FFI release that is not the last; empty drains skipped; drops of a variant with an unknown tag outlined | 2, 10 |
| #854 to #866, #919 | a borrow analysis: a call whose argument the caller keeps goes to a copy of the callee that does not retain or release it. On at the optimizing levels; `--disable-borrow-analysis` turns it off | the list of missing features at the end of this file |
| #852, #967 | the texture cache moved to a store for each user, keyed on paths | 25 (new) |
| #980 to #982 | on aarch64, compiled code reads the tag of a nullary variant from the pointer's top byte | 7, 10 (no encoding changes) |
| #983 | reference count intrinsics, `core::object::is_unique` | 10 |
| #988 | the rcgmp type through the C API; upstream's `Mpz` calls the C entry points directly | 20 |
| mlir-rcgmp pin `cc73b218` to `dee6c102` | mlir-rcgmp #51 to #53 | 20 |

Upstream closed the four issues that we filed: #759 (entry 19) and #760
(entry 23) on 2026-11-01, by the removal of retcon drops; #761 (the
executor's slot table and arena for each root drop) on 2026-10-21; #762
(borrowed parameters) on 2026-11-01, by the borrow analysis. Upstream's
design documents moved to another repository, so the patches have no
hunk in `docs/design` any more.

**2. The maintainer's port to `44abd17c` (lean2rr's pull request #4,
2026-11-05).** Reussir's maintainer moved lean2rr to upstream `44abd17c`
(2026-11-04) on the branch `port/upstream-worklist`, 7 commits on dev
`5d907046`:

- leanrt on upstream's drop scopes (`pending.rs`, `drop.rs`, `fs.rs`,
  `task.rs` and the model tests): a step returns `StepStatus`, a step or
  cell argument is never null, the end work is one scope-exit callback
  for each outermost scope, and `drain()` is gone.
- A series of 8 patches on `44abd17c`, with the new file `patches/base`:
  10-a, 07-a, 20-a, 20-c and 20-d moved (their messages cut to the
  subject), and three new ones: 24-a (a format repair of the moved 10-a
  and 20-c), 24-b (the integer glue kept out of the scoped drop
  lowering's records, one compile fix for 10-a, one style change in
  07-a, tests, and a clang-format of upstream's own lines) and 24-c (the
  tagged-handle rule in upstream's worklist drop expansion).
- 20-b, 20-e and 21-a left out of the series, and all of entry 23's
  patches, which upstream replaces.
- His checks: x86_64 only; the 18 classic programs at three sizes (54 of
  54); leanrt's unit tests of the pending work and of drops; 11 compiler
  tests. The runtime suite, the check scripts and aarch64 were not run.

**3. Our move to `36a55a0f` (2026-11-17).** 156 upstream commits after
`44abd17c`.

- *Moving the 8 patches.* 10-a, 07-a and 20-a applied with `git am -3`.
  20-c, 20-d and the three 24-x patches were cherry-picked from the
  series on `44abd17c`, with two conflicts: 20-c in `render_ty`
  (`crates/reussir-core/src/full/ffi.rs`: upstream added three arms next
  to the `BigInt` arm; both kept), and 24-b in an op list that it only
  wraps again. #988 (`rcgmp.rs`) merged with no conflict. No conflict
  came from #980 to #982, #968, #961 or #983.
- *Two new sites of 10-a's rule* (only the lowering of `rc.inc` and
  `rc.dec` may touch the count of a tagged handle), found by reading
  upstream's new code and shown with a repro each
  ([entry 10](10-tagged-ffi-objects.md#the-readers-of-a-count-on-36a55a0f)):
  the array task of the worklist drops under forward drop order, and
  `core::object::is_unique` (#983).
- *Folding.* A fix of our own patch is part of that patch, and a patch
  NN-x belongs to entry NN, so 24-a, 24-b and 24-c could not stay:
  24-a went into 10-a and 20-c (after the fold, neither has the format
  damage that it repaired); 24-b's three Rust changes and its test names
  went into 20-c, its C check into 20-d, its compile fix into 10-a, its
  mask constant into 07-a; 24-c and the two new fixes, with their tests,
  went into 10-a. 24-b's clang-format of upstream's own lines (about 110
  lines in `BasicOpsLowering.cpp` and `lib/CAPI/Types.cpp`) is not
  carried: it is not our code, and it conflicts at every move. The
  folded tree and the unfolded one differ only in those line breaks (61
  lines in, 63 out, one file; no token differs).
- *Messages.* Each patch has its body again (what, why, tests), brought
  up to date; the subjects are the maintainer's `[scope]` subjects.
- *Result.* Reussir branch `l2r-base13-folded`, head `d7952d77`, tree
  `fb321b62` (the unfolded branch `l2r-base13`: head `36e4cc97`, tree
  `0f9274c0`). The series applied to a clean `36a55a0f` gives the same
  tree.
- *Out of the series:* 20-b, 20-e, 21-a and 23-a to 23-p, moved to
  `patches/parked/` ([parked patches](#parked-patches)).
- *lean2rr's side.* The maintainer's leanrt changes are taken as they
  are (upstream's drop API did not change in shape after `44abd17c`),
  with the module documentation of the pending work written again.
  `scripts/l2r.py`: the checks named after the folded series;
  `--drop-order backward` passed explicitly; the texture cache keyed by
  the runtime build and kept in lean2rr's directory
  ([entry 25](25-texture-cache-key.md)); rustc wrappers hidden from
  cargo's build of lean-runtime again, unless `L2R_KEEP_RUSTC_WRAPPER=1`
  (the maintainer's port had removed that filter for his compiler
  cache). No change of the translator is expected.

Checks done on 2026-11-17 (all on aarch64):

- The unfolded tree builds (`rrc`, `reussir-rt`, `reussir-opt`,
  `reussir-translate`). `rustfmt --check` is clean on the 24 Rust files
  that the stack touches. clang-format was not run (the build machine
  has none); the C++ was formatted by hand.
- Reussir's lit tests that the stack adds or changes, 13 of 13. The
  three sanitizer tests were not run.
- Through lean2rr, on that build: three runtime tests (`RtNat`,
  `RtDropOrder`, `RtArray`) identical to native;
  `tests/runtime/texture-cache-check.sh`; `tests/runtime/any-probe.sh`
  (19 scenarios, both encodings of nullary variants);
  `tests/runtime/leanrt-unit.sh pending` (6 tests).
- Issue 24's repro on pristine `36a55a0f`: FIXED.

**4. The first gate, the refinement and the final series (2026-11-18).**

*The first gate* ran on the first series (Reussir `d7952d77`) with
lean2rr's translator of dev:

- Runtime suite: 739 of 747 identical to native, 2 expected failures
  (the same as before), 6 failures. All six are release order, with
  exit code and stderr identical; no build failure, no crash, no hang.
  Two of the six were documented differences that are gone (the output
  is native's now). The other four have two causes in upstream's drop
  design, both answered in lean2rr's emitter
  ([issue 2](02-native-drop-order.md#on-upstream-36a55a0f)).
- Check scripts: 21 of 22 pass. `rows-check` fails: rrc fails in the
  SVE storage pass on the row oracle's largest function
  ([issue 28](28-sve-vector-storage.md)). The scripts that pin shapes of
  the generated code (`sm-slots-check`, `ffi-inline-check`,
  `const-read-check`, `conv-count-check`, `inline-anchors-check`,
  `determinism-check`) have the output of the last gate on `l2r-base12`.
  `alloc-check` (81 tests, 191 rows): all inside their bounds.
- The classic corpus (passes on, 26 passes off, `unread-fields`), the
  raytracer: pass.
- `repros/run.sh`: [latest recorded run](#latest-recorded-run).
- Build time: the suite took 4048 s with a cold texture cache (the last
  gate on `l2r-base12`: 671 s with a warm one). With a warm cache a
  small program still takes more time in rrc and the link than on
  `l2r-base12`. The largest measured cause is in rrc's texture cache
  (the store is opened once for each texture); a change for it is under
  review and is not in the series.

*TRMC.* Upstream #984 keeps a self call in place when a call stands
between it and the constructor that takes its result. That fixes a
wrong order that lean2rr's programs had on `l2r-base12` (a traced
closure applied after a self call printed in the wrong order; now
test `RtTrmcCallOrder`). It also removed the loop from lean2rr's list
and tree maps, whose boxing of an element is such a call: over 26
programs, 57 functions had a TRMC helper on `l2r-base12` and 10 on
`36a55a0f`. lean2rr now binds such a box before the self call, and 54
of the 57 have a helper again (the other 3 are right to have none, or
need a wider rule). No Reussir change. Reading upstream's TRMC code for
this found the bug of [issue 26](26-trmc-observable-release.md).

*The series.* The five patches were reviewed and refined (branch
`l2r-base13-r2`): one predicate and a verifier rule for tagged handles,
20-g split from 20-a, three unused intrinsics removed, the integer glue
in every codegen unit with a module attribute for its visibility. 20-e
and 21-a were moved, measured and reviewed (21-a with a smaller rule).
Three upstream bugs were judged real, fixed and reviewed: 26-a, 27-a,
28-a. Result: Reussir branch `l2r-base13-final`, head `a5f5801f`, tree
`7070434f`, 11 commits on `36a55a0f` at that time (step 5 has the
final ids). The refinement, 20-e, 26-a, 27-a and
28-a change no instruction of 14 lean2rr programs; 21-a alone makes
every difference there, and each is a net removal.

*Checks on the final series:* the [review table](#review); through
lean2rr, 14 runtime tests identical to native, and `rows-check.sh`
passes (`every row agrees`).

*lean2rr's side after the first gate:* the two release-order rules and
the box hoisting (three new runtime tests, one new check script,
`trmc-helper-check.sh`); 258 runtime tests run again with the new
translator, all identical to native.

**5. The final gate (2026-11-18).** One more patch came into the
series after step 4: 29-a ([entry 29](29-texture-store-open.md)), the
answer to the largest measured cause of the first gate's build time.
It sits before the three bug fixes, so the series is our nine patches
and then the three fixes. Result: Reussir branch `l2r-base13-final`,
head `d62797ac`, tree `9066f3fc`, 12 commits on `36a55a0f`. After the
gate's compiler was built, the test of 29-a was changed on its
review's advice; the patch file has the new test, so the folder's
series gives tree `ccdf369d` (one test file differs, no compiler
source).

The gate (lean2rr `8d032fdb`, Reussir `d62797ac`, the texture store on
a memory file system):

- Runtime suite, 750 tests: 748 identical to native, 2 expected
  failures, 0 failures. The six failures of the first gate pass, and
  the three new tests pass.
- 23 of 23 check scripts; the classic corpus in its three modes; the
  raytracer; `repros/run.sh` on the series and on pristine upstream.
- The scripts that pin shapes of the generated code (`sm-slots-check`,
  `ffi-inline-check`, `const-read-check`, `conv-count-check`,
  `inline-anchors-check`, `determinism-check`) have the output of the
  last gate on `l2r-base12`. `alloc-check` (81 tests, 191 rows): all
  inside their bounds; the three rows that moved by more than a few
  allocations against `l2r-base12` are those of the first gate, with
  the same values, so they came with the base and not with the new
  translator.
- Build time: 1582 s for the suite; seven of the eight shards took 533
  to 687 s. One program, `RtOutlineStates`, takes 1079 s in rrc and the
  link (984 s in the first gate; its `.rr` is the same in both, and on
  `l2r-base12` the whole suite took 671 s). The cause is not known
  yet. Without that program the suite would take about 690 s.

Open after the port (each is recorded where it belongs):

- `RtOutlineStates` compiles in about 18 minutes on this base (cause
  under investigation).
- On large programs rrc uses more time than on `l2r-base12`
  ([entry 29](29-texture-store-open.md#what-stays-slower-than-on-l2r-base12));
  the cause is not attributed.
- `RtListDropWhole`, an array of 10^6 lists: peak 68.1 MB, 53.7 MB on
  `l2r-base12`; inside the test's allowance
  ([entry 23](23-worklist-drops.md#on-upstream-36a55a0f)).
- TRMC: one shape of lean2rr's code has no loop any more (a value
  built after the self call and boxed into the constructor, as in
  `AssocList.foldrM`); 54 of 57 functions have their loop again.
- Release order: a matched value that Reussir consumes alone in its
  `match` ([entry 2](02-native-drop-order.md#on-upstream-36a55a0f)).
- Wall time against `l2r-base12` and against native: pending the timing
  run.
- The deletion of entries 19, 23 and 24 (fixed upstream, to delete).

## History: the move to 95d9a1c8 (2026-10-26)

Upstream Reussir merged our pull requests #824 (`8130286e`), #843
(`20252b29`), #844 (`5aeb834d`) and #845 (`95d9a1c8`), with #825 to #828
between them (`e4b6aa84`, `59492889`, `0fb5ed0a`, `c2e7c0e2`: file locks
for rene, Reussir's package manager, and design documents of its
per-user cache). #824, #843 and #845 are 20-b (R2) split in three: the
handle `reussir_rt::rcgmp::Mpz`; the spelling of `Nat` and `Int` as
`Mpz` at polyffi type arguments, with the wrapper's releases; and the
tests at std's collections and the edge cases. Their code is 20-b's;
their tests are shorter, and #824 rewords the comments of `rcgmp.rs`.
#844 is 20-f's move of the mlir-rcgmp pin to `cc73b218`. `l2r-base12` is
`l2r-base11`'s series replayed on `95d9a1c8` (head `c1170ff9`, tree
`af82b837`; before, `l2r-base11`, `a39e59b0`, tree `eb79e76e`):

- 20-f left the series.
- 20-b keeps only the reviewed patch's tests that the pull requests left
  out: reussir-core's unit test of the spellings, two more properties of
  `frontend/bigint_ffi_generic.rr`, and the membership checks and the
  fuller header of `frontend/bigint_ffi_edge.rr`
  ([entry 20](20-rcgmp-integration.md#20-b-r2-nat-and-int-at-polyffi-type-arguments-are-an-owned-handle)).
- 20-c applied with one conflict, in a comment: it removes the words
  "through the rcgmp runtime's C entry points" from the module comment
  of `rcgmp.rs`, which #824 words differently; the resolved comment is
  upstream's without those words.
- The other 21 patches applied with no conflict. In their files only the
  commit ids, the patch counts (`[PATCH NN/24]`) and line offsets
  changed; 20-a, 20-d, 20-e and 21-a to 23-p have the same diffs.

Besides upstream's #825 to #828 (rene, `Cargo.lock`, documents), the
trees of `l2r-base11` and `l2r-base12` differ only in comments and
tests: the comments of `crates/reussir-rt/src/rcgmp.rs` (upstream's
wording), the header comment of `tests/integration/frontend/bigint_ffi_edge.rr`,
and the ASan twin `sanitizer/bigint-ffi-edge-asan.rr`, which is gone:
#845 runs the edge test under ASan inside `sanitizer/bigint-ffi-std-asan.rr`.
`cmake/RCGMP.cmake` is the same (`cc73b218`). No difference changes rrc,
reussir-rt or the code they generate. The other entries' *Upstream* lines
hold at `95d9a1c8` (no upstream commit since `00906e38` touches their
code); `scripts/l2r.py`'s checks pass on `l2r-base12` (R2's marker, the
`Mpz` struct, is upstream code now). The parked patches apply as before
(16-a and 19-a to `95d9a1c8` and `l2r-base12`; 01-a, 06-a and 06-b do
not). Checks on `l2r-base12` (2026-10-26): it builds with the settings
of the earlier bases (rcgmp on, mlir-rcgmp `cc73b218`); on a build of
the same commit with the tests and the ASan runtime, Reussir's lit tests
of drops, rcgmp and polyffi (87 selected: worklist, drop stack, drop
order, cell, retcon and tail drops, PIC, `bigint`, `rcgmp`, `polyffi`,
inc/dec cancellation, record drops) 83 passed and 4 unsupported (TSan,
the two builds without rcgmp, WASI); `reussir-ut` 82 of 82 (run from
the checkout, so that rustc is the pinned toolchain); reussir-core's
`bigint` unit tests 32 of 32, 20-b's included.

## History: the mlir-rcgmp pin (2026-10-26)

Upstream mlir-rcgmp's main gained #49 (vectorized heap paths of AND, OR
and XOR) and #50 (division without a remainder when only the quotient is
wanted), after the commit that upstream Reussir pins (`ca288d5e`, #804).
`l2r-base11` adds 20-f to entry 20, which moves the pin to `cc73b218`
(only `cmake/RCGMP.cmake`); head `a39e59b0`, tree `eb79e76e`; before,
`l2r-base10` (`0bea9c7d`, tree `707daa79`). lean2rr's L11 (bignum) runs
33.50G instructions instead of 40.10G (-16%), the count of lean2rr's
earlier leanrt representation. The runtime side built the 24 patches
before it unchanged and ran lean2rr's 28 `Nat` and `Int` runtime tests
and their alloc-checks: all pass. The other 24 patch files changed only
in their patch counts; the parked patches apply as before. 20-f is a
note under entry 20, not an entry of its own: it is no Reussir problem
(the old pin is correct, only slower) and no error in the library, which
is what entry 15's kind (a dependency issue) records, but a version
choice for the integers that entry 20 integrates, whose patches are what
lean2rr needs from Reussir's rcgmp side; every patch belongs to one
entry. It was dropped when upstream moved its pin, in #844
([the move to 95d9a1c8](#history-the-move-to-95d9a1c8-2026-10-26)).

## History: linked pending records (2026-10-26)

The review of the shared stack (23-k to 23-m) measured a shape where
its entries cost memory: a chain of two mutually recursive types whose
levels each leave a record of the other type pending (lean2rr's
`RtAltTreeFree`) took a 24-byte entry per level while it waited, 88.7 MB
at 10^6 levels against native Lean's 55.1 MB and dev's 45.7 MB on
`l2r-base8` (whose drop patches linked pending records through their
headers). `l2r-base10` adds three patches to entry 23: 23-n (pending
records of the glue linked through their own headers, `defer_wide`),
23-o (the glue's use of it for boxes with a wide header) and 23-p (one
release function's pending records as a run of cells, for fewer
instructions; only a change of function links). Head `0bea9c7d`, tree
`707daa79`; before, `l2r-base9-shared` (`6111586c`, tree `8b8dd1cb`).
The other 21 patch files changed only in their patch counts.
`RtAltTreeFree` now peaks at 45.7 MB (its bounds are native's, lean2rr's
branch alt-tree-bounds), and `scripts/l2r.py` requires 23-n and 23-o.
The parked patches apply as before (16-a and 19-a to `l2r-base10`; 01-a,
06-a and 06-b do not).

## History: Phase 2, worklist drops instead of the local drop patches (2026-10-25)

Phase 2 moves lean2rr off the local drop patches. lean2rr's runtime
(leanrt) keeps its own stack of pending releases for its own objects
(the port of leanrt-v1), so the patches that shared Reussir's stack with
leanrt went: a Reussir change is the last resort (owner). Reussir frees
Direct and TailLoop records with upstream's glue, and the other
recursive records through entry 23's worklist, on a stack that leanrt
shares. The base is `l2r-base9-shared`: upstream `00906e38` plus 10-a,
07-a, entry 20's five, 21-a and 23-a to 23-m (head `6111586c`, tree
`8b8dd1cb`; before, `l2r-base8`, head `8e9a6293`, with 14 patches).
`l2r-base9` (head `fc9c1d20`, tree `8c53abcf`) was its first version,
without 23-k to 23-m.

- **02-a to 02-e and 09-a left the series.** They replaced upstream's
  drop lowering with a stack shared with leanrt (02-a to 02-e) and added
  a hook at the end of its drain (09-a). The other patches apply with no
  conflict and no change of code; in their files only the commit ids,
  the patch counts and line offsets changed. 02-b's update of upstream's
  `glue_symbols.cpp` went with 02-b; 10-a keeps its two-parameter
  builder.
- **Entry 2 stays, not patched**, as an open difference from native
  Lean's order ([issue 2](02-native-drop-order.md)). Its repros now
  check the bounded depth that upstream and entry 23 give; the Miri test
  of 02-c's stack was deleted.
- **Entry 9 (the drain-end hook) was deleted and its number retired.**
  leanrt's own stack runs the end work when its outermost free ends
  (`pending::want_end_work`, `task::drained`), so lean2rr needs no
  Reussir hook.
- **Entry 11 (the cost of freeing one cell through 02-b's stack) was
  deleted with its parked patch 11-a, and its number retired:** that
  stack is gone.
- **Retcon drops, entries 19, 22 and 23.** Phase 2's first base,
  `l2r-base7` (upstream `00906e38` plus 10-a, 07-a, 19-a and entry 20's
  five; head `bfe3d32d`), used upstream's retcon drops, which 02-a had
  turned off. Two problems showed there: the drop expansion ran out of
  memory on lean2rr's programs (entry 19, upstream #759; patch 19-a,
  option (a+), which the maintainer chose and asked to keep local), and
  freeing a deep value kept one coroutine frame per level (entry 23:
  `RtClosureChainFree` 652 MB, native 102 MB). A first local attempt at
  the second, retcon destructors that share their suspend points
  (`l2r-mergesusp`, never published, number 22), was dropped for entry
  23's worklist drops, which replace the retcon drops in rrc's
  pipelines. So 19-a is no longer reached and is parked; entry 19 stays,
  an open upstream bug. Entry 22's number is retired.
- **Entry 24 is new:** a leak with TPDE's drop options that entry 23's
  review found, fixed inside 23-e.
- **23-k to 23-m: one stack for Reussir's glue and leanrt.** With 23-a
  to 23-j only (`l2r-base9`), Reussir's drain and leanrt's stack were
  separate, and leanrt ran Lean code inside Reussir's drain (a promise's
  dependents, its own end work), whose frees of Worklist records only
  joined the drain: a promise dropped that way was not resolved
  (lean2rr's `RtPromiseDepFreeInDrain`) and code waiting for it hung
  (`RtPromiseDepWaitInDrain`), and a tree's handles inside an array
  closed per subtree (`RtDropOrderRec`). The runtime side added end work
  after the outermost drain (23-k), runs of cells (23-l) and steps,
  depth and drain for a host (23-m), and built leanrt's pending stack
  on Reussir's; the three tests then give native's results
  ([issue 23](23-worklist-drops.md#the-shared-stack-23-k-23-l-23-m)).
- **`scripts/l2r.py`** requires 23-f, 23-k, 23-m and 07-a; it required
  02-a, 09-a, 07-a and 02-e, and checked that upstream's tail-recursive
  and retcon drops were off.
- **New repros:** `bug19-retcon-direct-arms.py`, `bug23-deep-free.rr`
  (with its C driver) and `bug24-locked-drop-token.mlir`: FIXED on
  `l2r-base9` and `l2r-base9-shared` (24: `l2r-base9`), REPRODUCES on
  `00906e38`.
- **The parked patches:** 16-a and 19-a apply to `l2r-base9-shared`;
  01-a, 06-a and 06-b do not, as before.
- **Release order through lean2rr** (2026-10-25, Phase 2's runtime): on
  `l2r-base9`, 26 of 27 release-order and deep-free tests of lean2rr's
  runtime suite gave native output, all but `RtDropOrderRec` (above); on
  `l2r-base9-shared` the runtime side reports `RtDropOrderRec` native
  again, `RtDeepTreeFree` and `RtClosureChainFree` within their
  alloc-check bounds, and the two end-work tests passing (lean2rr's
  phase2-dev, commits `fbd9f1c2`, `d502cd7d` and `92512534`).

Phase 2 was prepared on stacks before this one: `l2r-base4`
(`545499c8`: upstream `7954a367` plus 05-a, 10-a and 07-a; the first
port, which waited for #759), `l2r-base6` (`9f9073a3`: upstream
`ea240b19` plus 10-a, 07-a and 19-a), `l2r-base7` and `l2r-base9`
(above).

## History: entry 21 (2026-10-25)

A profile of lean2rr's rcgmp backend found that inc/dec cancellation
keeps the retain of an integer member extracted from a `[value]` record
and the member's release in the record's drop, a pair it cancels for an
rc member. Entry 21 records it, and patch 21-a cancels the pair under the
same rules ([entry 21](21-value-record-member-retains.md)).

- The patch was made on lean2rr's planned base for Phase 2 and taken to
  `l2r-stepd` with no conflict: `./reussir`'s head `8e9a6293` is
  `l2r-stepd` plus 21-a, and the series of 14 on `00906e38` gives its
  tree, `10b34f74`.
- The other 13 patch files did not change. The parked patches apply as
  before (11-a with the series of 14, 16-a to the stack; 01-a, 06-a and
  06-b do not).
- On that stack, Reussir's lit suite has the results it has without
  21-a, apart from the new tests, and `reussir-ut` passes 82 of 82.

## History: step D patches published (2026-10-25)

lean2rr's clean-integration step D puts Lean's `Nat` and `Int` on
Reussir's built-in rcgmp integers (`--int-backend rcgmp`). Its Reussir
patches R1, R2, R2b, R2c and R3 were made and reviewed on `l2r-stepd`
and are published here as entry 20, patches 20-a to 20-e, after the 8
patches before them: the series has 13 patches, `l2r-stepd` is
`00906e38` plus the 13 commits (head `e3b96e03`, tree `b3b19387`). They
apply with no conflict.

- Entry 20 is new; number 19 stays reserved for the Phase 2 base's patch
  for upstream issue #759 (option a+), which is not in the series. The
  next free number is 21.
- 02-b and 10-a also changed, for Reussir's C++ unit tests, which now
  build and pass (82 of 82): 02-b updates upstream's `glue_symbols.cpp`,
  and 10-a adds a two-parameter `FFIObjectType` builder for upstream's
  `record_drop.cpp` (entries 2 and 10). rrc's code is the same. In the
  other 6 files only the commit ids, the patch counts (with the wrapping
  of two subject lines) and, in 07-a, the blob ids of `ReussirTypes.td`
  changed.
- Reussir's maintainer takes these patches from this directory (see
  [Policy](#policy)); entry 20 explains each one with its tests and the
  measured effects.
- The parked patches apply as before (11-a with the series of 13, 16-a
  to `00906e38` and `l2r-stepd`; 01-a, 06-a and 06-b do not).

## History: the move to 00906e38 (2026-10-25)

Upstream `00906e38` (#804, 2026-10-25), the only upstream commit after
`ea240b19`, moves the commit of mlir-rcgmp that Reussir's build fetches
(`cmake/RCGMP.cmake`, `GIT_TAG`) from `c2a68d81` to `ca288d5e`. That
mlir-rcgmp commit has #48: shorter fast paths for immediates in rcgmp's
integer operations, upstream's answer to our mlir-rcgmp #47. `l2r-base5`
became `00906e38` plus the same 8 commits (head `c4a5df4b`, tree
`402845d1`; before, head `e1680f65`, tree `734cf027` on `ea240b19`).
They apply with no conflict; in their patch files only the commit ids
changed.

No entry is affected and no patch changed: `00906e38` changes only the
build file, and lean2rr's programs use no rcgmp integers (their `Nat`
and `Int` are tagged FFI handles, 10-a), so the code that rrc makes for
them does not change. The parked patches apply as before (11-a with the
series, 16-a to `00906e38` and `l2r-base5`; 01-a, 06-a and 06-b do not).

## History: the move to ea240b19 (2026-10-25)

Upstream merged our pull request #758 as `ea240b19` (2026-10-25), the
only upstream commit after `0378b744`. It has the change of patch 05-a:
when `--relocation-mode` is `default`, `rrc --emit executable` and
`--emit dynlib` compile position-independent code. An explicit mode is
kept, and the other outputs keep the default of the target. Upstream
fixes entry 5 in full, so:

- 05-a is not in the series any more: `l2r-base5` became `ea240b19`
  plus the other 8 commits (head `e1680f65`, tree `734cf027`; before, head
  `6bf9be85`, tree `cb4c6d48` on `0378b744`). They apply with no
  conflict; in their patch files only the commit ids and the patch
  counts changed.
- Entry 5 and its repro (`repros/bug05-executable-textrel.rr`, its
  function in `run.sh`) are deleted. Number 5 is retired: the other
  entries keep their numbers, and the next free number stays 19. The
  deleted files are in git history (commit `0f9e1b05`; see
  [names](#names)).
- lean2rr's workaround stays: `scripts/l2r.py` still passes
  `--relocation-mode pic`. On `ea240b19` and later this is rrc's
  default for executables, so the flag is redundant but harmless; it
  stays for older bases. `tests/runtime/run.sh` still fails a test whose
  executable has text relocations.

Nothing else changed: `ea240b19` touches only rrc's driver
(`driver.rs`, `driver/cli.rs`), the CHANGELOG and two codegen tests
(`executable_pic_default.rr`, `executable_pic_default_retcon.rr`), and
no code of another entry. The parked patches apply as before (11-a with
the series, 16-a to `ea240b19` and `l2r-base5`; 01-a, 06-a and 06-b do
not).

## History: the move to 0378b744 (2026-10-24)

Upstream Reussir moved from `7954a367` to `0378b744` (43 commits). Most
of them add the built-in `Nat` and `Int` on rcgmp (#770 to #803). The
others add a registry of optional compiler features (#766 to #768), pin
TPDE (#765), add PJRT parts (#764, #769) and constant sequences of
aggregates (#754, #755), and change the drop executor (#763). The 9
patches of the series applied with no conflict: `l2r-base5` is
`0378b744` plus the same 9 commits. No entry is fixed, so no entry was
deleted and no number changed.

Upstream commits that touch the code of an entry:

| Commit | Change | Entry | Effect on the entry |
|---|---|---|---|
| #763 `fe9f2379` | the executor of retcon drops keeps its slot table and arena for each thread between root drops (it fixes upstream issue #761) | 2, 9 | none: 02-a turns retcon drops off in lean2rr's builds; upstream still has no host deferral, no stack that a host can share and no drain-end hook |
| #800 `810849d6` | after the acquire/drop expansion, a load is replaced by an equivalent load that dominates it | 3 | none: the first phase still writes the copy of a `[value]` record out in line; only line numbers in `pipeline.rs` moved |
| #790 `e2f41986`, #801 `7cb5f58c` | the drop expansion and the inc/dec cancellation handle rcgmp integer members | 2 | none: lean2rr's `Nat` and `Int` are tagged FFI handles (10-a), not rcgmp integers |
| #776 `af25863e` (with #770 to #803) | built-in `Nat` and `Int`: a small value is an immediate, a large one a counted heap object | 10 | not a fix: an opaque FFI handle must still be a pointer; the built-in types are another way to a one-word `Nat` and `Int`, which lean2rr does not use yet |

The other entries' code has no change: token reuse (1, 8), the MLIR
printer (4), the relocation model of rrc's linked products (5; #772
only adds the rcgmp runtime to the link), import trampolines (6), the
inline count increment of a tagged handle (7),
reussir-rt's `nullable.rs` and its small-allocation path (12, 13; #771
adds only rcgmp's allocation hooks to `alloc.rs`), `formatInto` (14),
the `libmimalloc-sys` pin (15, still 0.1.44), the 1 GiB driver stack
(16) and the record layout (17, 18; the type converter only adds the
rcgmp types). Pull request #758 (05-a) is still open (upstream merged
it on 2026-10-25 as `ea240b19`: [the next move](#history-the-move-to-ea240b19-2026-10-25)).

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
| 34 | 5 (retired 2026-10-25) | | | 45, 46 | 14, 15 |
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
  when dropped ([issue 2](02-native-drop-order.md); plan §10).
- **Drop glue that may not return.** Reussir marks drop glue `mustprogress
  nounwind willreturn`. Through lean2rr's runtime (the release hooks that
  Reussir's glue calls, and the end work of leanrt's outermost free) a
  free can run Lean continuations, which might not return
  (`IO.Process.exit` inside a sync dependent), which would falsify
  `willreturn`. No concrete miscompile was found. (Review RV8, side note
  on 40-a, later 09-a, which Phase 2 removed; the end work is leanrt's
  own now.) 23-b declared the drop stack's two runtime functions
  `nounwind` only, since their callbacks run arbitrary drop glue (not
  rechecked for upstream's drop functions at `36a55a0f`).
- **TokenReuse's locality bonus is dead code (not a bug).** In
  `lib/Transformation/TokenReuse/TokenReuse.cpp`, function `heuristic`,
  the walk from a new cell's field back to the cell it was loaded from
  steps to `dispatch.getValue()` where the scrutinee (`getVariant()`) is
  meant, and the field list it starts from is read from the `rc.create`
  itself, so the list is always empty and the bonus never applies (a
  missed optimization; with only the first mistake corrected,
  `reussir-opt --reussir-token-reuse` crashes on a result-less dispatch).
  Not rechecked on `7954a367`; token reuse has no change up to
  `0378b744`, and not rechecked on `36a55a0f`. [Issue 8](08-alias-release-donor.md) is a
  case where the bonus would decide for the matched cell.

## Missing features that cost lean2rr performance

Not bugs, but each one costs lean2rr measurably:

- **Borrowed parameters** (in part done upstream). Reads of arrays and
  strings through the runtime take the container owned, so each read
  retains and releases it. Traversals that keep unchanged nodes paid the
  same on fields (about 1.5x native on an `Expr.replace`-style DAG
  traversal, on the bases up to `l2r-base12`). Reported upstream as issue
  #762, which upstream closed on 2026-11-01 with a borrow analysis (#854
  to #866, #919; on by default at `36a55a0f`): a Reussir function whose
  caller keeps the argument gets a copy that does not retain or release
  it. The analysis works on Reussir functions with a body, so a read
  through a texture is not covered by it (by reading). Its effect on
  lean2rr's programs: pending the timing run.
- **A one-word `Nat`** (done: lean2rr's `Nat` and `Int` are Reussir's
  built-in integers since D8, 2026-10-26; before, local patch 10-a,
  [issue 10](10-tagged-ffi-objects.md), made them one tagged word, as
  natively; the box `LAny` still uses tagged handles).
- **`[value]` types across the FFI.** Arrays of enumerations or `[value]`
  records need runtime-side representations or wrappers.
- **Guaranteed tail calls.** Mutual tail calls are sibling calls only when
  all arguments fit in registers.
