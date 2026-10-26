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

**Base.** lean2rr's Reussir is upstream Reussir `00906e38` (`main` on
2026-10-25) plus the 21 patches of the series: 10-a, 07-a, entry 20's
five, 21-a and entry 23's thirteen. The checkout at `./reussir` is not
part of this repository; its branch `l2r-base9-shared` (head `6111586c`)
is that stack (the series gives the same tree, `8b8dd1cb`), and
`scripts/l2r.py`
stops with an error on a Reussir without the patches it requires
([applying the patches](#applying-the-patches)). Since `0378b744`, the
base needs GMP and newer build tools
([building Reussir](#building-reussir)).

`l2r-base9-shared` is Phase 2's base (2026-10-25). Reussir frees Direct
and TailLoop records with upstream's glue and the other recursive
records through the per-thread drop stack of entry 23 (worklist drops),
and lean2rr's runtime keeps its pending releases on that same stack
(23-k to 23-m). `./reussir`'s branch `l2r-base9` (head `fc9c1d20`, tree
`8c53abcf`) is the same series without 23-k to 23-m. So the local
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

- **Entry numbers** run from 1 to 24. Numbers 5, 9, 11 and 22 are
  retired (2026-10-25): upstream `ea240b19` fixed entry 5 in full; Phase
  2 made entries 9 and 11 obsolete (they were about the drop series'
  shared stack, which is gone); and number 22 named a local patch that
  was never published here (retcon destructors that share their suspend
  points, `./reussir`'s branch `l2r-mergesusp`, commit `a8f3fc70`), which
  entry 23 superseded: with 23-f no pipeline makes retcon destructors. No
  other entry gets these numbers; the other entries keep theirs. Number
  19, reserved until Phase 2 for the patch for upstream issue #759, is
  that entry. The next free number is 25. (Old number 37 was
  reserved for another track's patch, value records across the FFI
  boundary; that track takes the next free number.)
- **A patch file** is named `NN-x-slug.patch`. NN is the number of its
  entry. The letter x gives the order of the entry's patches (a, b, c,
  ...). The slug is a short description. Every patch belongs to exactly one
  entry. In the text, a patch is named by NN-x: 20-b is the second patch of
  issue 20.
- **Patch file contents** are `git format-patch` output of the commits of
  `l2r-base9-shared`, against `00906e38`, as one series (each subject has
  its patch count, `[PATCH NN/21]`). A file's subject line is the subject of
  its commit: "issue 38" (an old number) means entry 7; 10-a's subject
  has no number; the subjects of 20-a to 20-e name step D's patches R1,
  R2, R2b, R2c and R3 (entry 20); those of 21-a and 23-a to 23-m name
  their entries. The parked 19-a is its file from `l2r-base7`'s series
  (`[PATCH 3/8]`). The
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

## Status

One row per entry, grouped by kind. Column *Patches*: the entry's patch
files in the series, or "none", or a parked patch
([parked patches](#parked-patches)). Column *Upstream*: what upstream
`00906e38` does about it. "Checked" means a check on `7954a367` on
2026-10-19 (a repro run, or the source read). On 2026-10-24 the code of
each entry was compared with `0378b744`: no upstream commit since
`7954a367` fixes an entry
([history](#history-the-move-to-0378b744-2026-10-24)); each entry's
*Upstream* line gives the details. The two upstream commits after
`0378b744` (both 2026-10-25) change no code of another entry, so the
*Upstream* lines of the entries are true for `00906e38` too:
`ea240b19` changes only the default relocation model of rrc's linked
products and fixes entry 5 in full (deleted, its number retired;
[history](#history-the-move-to-ea240b19-2026-10-25)), and `00906e38`
changes only the commit of mlir-rcgmp that the build fetches
([history](#history-the-move-to-00906e38-2026-10-25)).

| # | Kind | Effect | Affects lean2rr output? | lean2rr workaround | Patches | Upstream |
|---|---|---|---|---|---|---|
| [12](12-nullable-as-ref.md) | bug | reussir-rt's `Nullable::as_ref` returns a reference to a local copy of the pointer word (dangling) | no: nothing calls it | - | none | unchanged; repro fails (checked) |
| [13](13-small-allocation-limit.md) | bug (32-bit targets) | constant-size boxes of 513 to 1024 bytes go to `mi_malloc_small`, whose limit is 512 bytes there | no: 64-bit targets only | - | none | unchanged (checked) |
| [14](14-polyffi-rc-substitution.md) | bug (hand-written MLIR only) | a polymorphic-FFI substitution given as an MLIR rc type becomes Rust's `Rc` without the record's glue | no | - | none | unchanged (source read at `0378b744`) |
| [16](16-driver-stack-address-limit.md) | bug (under `ulimit -v`) | rrc's 1 GiB driver stack (#686) counts against an address-space limit: under `ulimit -v` 1250000 or 1600000 rrc aborts where it compiled before | no: lean2rr sets no such limit | - | none (parked: [16-a](patches/parked/16-a-driver-stack-rlimit.patch)) | open: #686 is the old 31-a; no pull request planned |
| [19](19-retcon-direct-arms.md) | bug (rrc out of memory) | the drop expansion writes a retcon variant's direct arms out in place at every drop site, nested types included: code exponential in type nesting (#759) | no since `l2r-base9`: rrc makes no retcon destructors (23-f); on Phase 2's first base (`l2r-base7`) rrc ran out of memory on `RtSyncSelect` without the patch | - | none (parked: [19-a](patches/parked/19-a-retcon-direct-arms.patch)) | open (#759); the maintainer chose option (a+), 19-a, and asked that it stay local |
| [24](24-locked-drop-token-leak.md) | bug (a leak, with TPDE's drop options) | with tail-recursive and retcon drops off, a lock-guarded cell's payload is released inside the critical section, and its box is never freed | no: rrc has no TPDE level | - | fixed by [23-e](patches/23-e-worklist-nullable-locked.patch) | open; not reported |
| [3](03-value-record-dag.md) | cost (deliberate design) | the first acquire/drop expansion writes a `[value]` record's copy out in line, exponential for records shared in a DAG | no, lean2rr's `[value]` records are shallow | - | none | still reproduces (checked) |
| [4](04-emit-mlir-size.md) | cost (debug output) | the `--emit mlir` dump is exponential in the nesting of records that share sub-records | no, builds unaffected | dump smaller programs | none | still reproduces (checked) |
| [23](23-worklist-drops.md) | cost (memory and run time) | retcon destructors keep one coroutine frame per level of a value being freed: memory grows with the depth (85 to 622 bytes per level) | yes: peak memory of deep frees (`RtClosureChainFree` 652 MB on `l2r-base7`, native 102 MB) and instructions per freed cell | none | [23-a](patches/23-a-drop-stack-runtime.patch) to [23-m](patches/23-m-drop-stack-steps.patch) (thirteen; 23-k to 23-m share the stack with leanrt) | by design (retcon drops, #678, #679); not reported |
| [1](01-phantom-reuse-donor.md) | missed optimization | token reuse picks decrements that never free | yes, speed | fields bound lazily (`lazy-fields`) | none (parked: [01-a](patches/parked/01-a-sink-bound-retains.patch)) | not rechecked; no change to token reuse up to `0378b744` |
| [6](06-trampoline-inline.md) | missed optimization | a texture's import trampoline has no inline attribute: at a cold call site a texture costing more than 45 stays a call | yes, speed (three reads at cold sites) | read textures kept small | none (parked: [06-a](patches/parked/06-a-inline-small-textures.patch), [06-b](patches/parked/06-b-inline-guards.patch)) | still reproduces (checked) |
| [17](17-padded-member-widening.md) | missed optimization | with `--no-pack-record-members`, a member padded by the next one's alignment is widened to an integer but stored at its own width (`store i1`): LLVM keeps the struct on the stack | yes, speed (generated tuples with a `bool` first) | every generated tuple (join points, `flatten-structs`) in decreasing alignment (`memberOrder`) | none | found on 7954a367 with the series; unchanged at `0378b744`; not reported |
| [18](18-tail-padding-return.md) | missed optimization | a `[value]` struct's tail padding is an explicit byte array in the LLVM struct (`{ i64, i1, [7 x i8] }`); each byte counts as a returned value, so on aarch64 a result with more than 8 values comes back in memory (`sret`) | yes, speed (Unionfind +16% instructions on dev b874c365) | the tuple of a `flatten-structs` result keeps narrow values in `u64` members and no unit member (`tupleMemberTy`) | none | found on 7954a367 with the series; unchanged at `0378b744`; not reported |
| [21](21-value-record-member-retains.md) | missed optimization | inc/dec cancellation keeps the retain of an rcgmp integer member extracted from a `[value]` record or tuple, and the member's release in the record's drop, a pair it cancels for an rc member | yes, under `--int-backend rcgmp`: speed (L12 -9.6% instructions, L17 -7.8%, Z01c -6.0%) | none | [21-a](patches/21-a-value-record-member-retains.patch) | not upstream; prepared as a pull request candidate, not opened |
| [8](08-alias-release-donor.md) | missed optimization | token reuse takes the release of a value an opaque call returned (an alias, never freed) as the donor | no longer | a field put back into a rebuilt node is boxed again | none | still reproduces (checked) |
| [2](02-native-drop-order.md) | missing feature (partly fixed upstream) | drop glue does not free in native Lean's order: upstream frees first field first; with entry 23, a Worklist record's other members at its visit and its dead children last first | yes: the release order of resources when user code drops a record; accepted by the owner | leanrt keeps its pending releases on entry 23's stack, which gives native order inside every drain | none since Phase 2 (02-a to 02-e left the series) | the stack depth is fixed (#677 to #679, another design, first field first); the order is not |
| [7](07-tagged-top-bits.md) | missing feature | the inline count increment of a `tagged` handle uses all 64 bits as the address | yes: the one-word `Box` needs it | none | [07-a](patches/07-a-tagged-top-bits.patch) | not fixed |
| [10](10-tagged-ffi-objects.md) | missing feature | an opaque FFI handle must be a pointer to a counted box: it cannot be an immediate | yes: the one-word `Nat` and `Int` need it | none | [10-a](patches/10-a-tagged-ffi-objects.patch) | not fixed (upstream's built-in `Nat` and `Int`, #776, are another way to one word; lean2rr does not use them) |
| [20](20-rcgmp-integration.md) | missing feature (one patch also fixes a bug) | Reussir's built-in `Nat` and `Int` (rcgmp) lack what lean2rr's `Nat` and `Int` on rcgmp need: intrinsics for Lean's division modes and the power-of-two remainder, an owned handle at polyffi type arguments (without it a leak and uses after free, a bug), retain and release glue that inlines into textures, a query for sharing, and a parse of big literals that is not cubic | yes, under `--int-backend rcgmp` (step D) | none | [20-a](patches/20-a-bigint-lean-division.patch), [20-b](patches/20-b-mpz-polyffi-handle.patch), [20-c](patches/20-c-mpz-inline-glue.patch), [20-d](patches/20-d-mpz-is-shared.patch), [20-e](patches/20-e-hex-bigint-literals.patch) | not upstream; Reussir's maintainer takes them from here; prepared as pull request candidates, not opened |
| [15](15-mimalloc-arena-purge.md) | issue (dependency: mimalloc v2.2.4) | mimalloc's delayed arena purges do not run | yes, peak memory | leanrt sets `arena_purge_mult` to 0 on v2.1.8 to v2.2.7 | none (a newer `libmimalloc-sys` parked) | unchanged (still 0.1.44; checked) |

**Counts.** 20 entries (numbers 1 to 24; numbers 5, 9, 11 and 22 are
retired): 6 bugs, 3 costs, 6 missed optimizations, 4 missing features, 1
dependency issue. 5 entries have patches in the series, 21 patch files
in all (one each for 7, 10 and 21, five for entry 20, thirteen for entry
23): 6 features (07-a, 10-a, 20-a, 20-d, 23-k, 23-m), 2 patches that
also fix a bug (20-b, a feature that lean2rr needs; 23-e, an
optimization that fixes entry 24), 11 optimizations (20-c, 20-e, 21-a,
23-a, 23-b, 23-d, 23-f, 23-h, 23-i, 23-j, 23-l), a refactor (23-c) and
a patch of tests (23-g). 5 parked patches lie outside the series (01-a,
06-a, 06-b, 16-a, 19-a).

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
git -C reussir checkout -b l2r-base9-shared 00906e38
while read -r p; do
    git -C reussir am "$PWD/reussir-bugs/patches/$p" || break
done < reussir-bugs/patches/series
cmake --build reussir/build --target rrc reussir-rt
```

Checked on 2026-10-25 (`git am` in a throwaway worktree): the series on
`00906e38` gives tree `8b8dd1cb`, the tree of `./reussir`'s
`l2r-base9-shared` (`6111586c`); without 23-k to 23-m it gave
`l2r-base9`'s tree, `8c53abcf` (`fc9c1d20`). Phase 2's first base,
`l2r-base7` (upstream `00906e38` plus 10-a, 07-a, 19-a and entry 20's
five; head `bfe3d32d`, tree `eeab2856`), never became lean2rr's
published base; `l2r-base9-shared` is it without 19-a, with 21-a and
entry 23's patches. Before Phase 2, the
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

Order and dependencies:

- 07-a needs 10-a (the tagged handles whose increment it masks).
- 20-a to 20-e come after them, in that order. 20-c and 20-d change
  20-b's `Mpz`, and 20-d adds a function to 20-c's glue; 20-e changes
  code next to 20-a's (`lower/expr/bigint.rs`, the backend's
  `rcgmp.rs`).
- 21-a changes no file of another patch (inc/dec cancellation, the
  equivalence analysis, `RCGMPMembers.cpp` and `ReussirOps.h`); it
  applies to `00906e38` and to the series alike.
- 23-a to 23-m come last, in that order: 23-b lowers to 23-a's runtime
  functions, 23-d uses 23-b's ops and 23-c's helper, 23-e to 23-j change
  23-d's glue (`WorklistDrop.cpp`), 23-f switches the pipelines, and
  23-k to 23-m change only 23-a's runtime stack (`drop_stack.rs`), each
  on the one before. 23-a to 23-j also apply to `00906e38` alone (`git
  am`, 2026-10-25).
- The series is the order in which the patches were made, not entry
  order.

What lean2rr needs: `scripts/l2r.py` stops with an error when the
Reussir checkout lacks 23-f (rrc's pipeline with worklist drops), 23-k
(the end work), 23-m (steps, depth and drain) or 07-a
(`REQUIRED_REUSSIR_PATCHES`), so plain upstream fails there, and so do
the checkout of a base before Phase 2 (its glue pushed onto the old
shared stack) and `l2r-base9`; leanrt's pending stack, built on entry
23's, does not compile without 23-k to 23-m; its prelude needs 10-a (it
declares `Nat` and `Int` `tagged`). lean2rr's `--int-backend rcgmp`
(step D, on dev since `1e57ed53`) needs 20-a and 20-b (its `check_rcgmp`
checks for them) and uses 20-c to 20-e and 21-a. rcgmp is lean2rr's
default representation since 2026-10-25, so a default build needs them;
`--int-backend leanrt` (`L2R_INT_BACKEND=leanrt`) does not. 21-a is an
optimization: nothing requires it, and `scripts/l2r.py` does not check
for it. The driver also passes `--relocation-mode pic`, the workaround
for entry 5 (retired): since `ea240b19` this is rrc's default for
executables, so the flag is redundant but harmless; it stays for older
bases.

**Adding a patch.** Name the file after its entry: `NN-x-slug.patch`, with
the next free letter of the entry (a new problem gets the next free entry
number, 25). Put it in `patches/` and add its name as the last line of
`patches/series`. Write the *Patch* and *Upstream note* sections of the
entry's file, and update the entry's row in the status table. Add a row to
the [review table](#review) when its review is done.

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
  commit that `cmake/RCGMP.cmake` pins (`GIT_TAG`; `ca288d5e` since
  `00906e38`, `c2a68d81` before). An offline build needs them there
  first.

After a change of the C++ headers (for example after you install
`libstdc++-14-dev`), delete the build directory and configure again. The
C++ module files (`.pcm`) that the old headers made stay in the build
directory, and the build then fails with "ambiguous deduction for
std::span".

### Parked patches

A parked patch was made and reviewed, but lean2rr's builds do not apply
it: the owner removed it from the series. Its file is in
[`patches/parked/`](patches/parked/), outside
[`patches/series`](patches/series) and the counts above; its entry says
why it is parked and describes the patch.

| Patch | Entry | Kind | Parked | Why | On 00906e38 |
|---|---|---|---|---|---|
| [01-a](patches/parked/01-a-sink-bound-retains.patch) | [1](01-phantom-reuse-donor.md) | optimization | 2026-10-07 | a missed optimization; lean2rr's `lazy-fields` covers it | does not apply |
| [06-a](patches/parked/06-a-inline-small-textures.patch), [06-b](patches/parked/06-b-inline-guards.patch) (review fixes) | [6](06-trampoline-inline.md) | optimization | 2026-10-07 | the gain is too small for a local Reussir patch | do not apply |
| [16-a](patches/parked/16-a-driver-stack-rlimit.patch) | [16](16-driver-stack-address-limit.md) | bug fix | 2026-10-19 | lean2rr does not reach the bug | applies to `00906e38`, `l2r-base5`, `l2r-stepd`, the series of 14, `l2r-base9` and `l2r-base9-shared` |
| [19-a](patches/parked/19-a-retcon-direct-arms.patch) | [19](19-retcon-direct-arms.md) | bug fix | 2026-10-25 | lean2rr does not reach the bug since 23-f (rrc makes no retcon destructors) | applies to `00906e38`, `l2r-base9` and `l2r-base9-shared` |

The parked files 01-a, 06-a and 06-b are against the stacks they were
made on (`ef922049` plus earlier patches of the old series); 16-a is
against `7954a367`, 19-a against `l2r-base7` (`00906e38` plus 10-a and
07-a). The column *On 00906e38* was checked on 2026-10-25 (`git apply
--check`; on `0378b744` on 2026-10-24 and on `ea240b19` on 2026-10-25,
with the same results; with the series of 13 patches, the series of 14
and `l2r-base9-shared` on 2026-10-25, the same results). The parked 11-a was
deleted with entry 11 in Phase 2 (it needed 02-c and 09-a). To park a
patch of the series, move its file to `patches/parked/`, delete its line
from `patches/series`, rebuild the Reussir stack from the series, and
update the entry, its row and the counts.

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
have no repro. 10 and 20 are missing features that show only through a
host that uses them, and their patches carry their own tests (20-b's
tests also show its bug: they fail with `l2r-base5`). 21's patch has a
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
On Phase 2's first base `l2r-base7`, issue 19's repro printed FIXED
with 19-a (322 KB and 457 KB, 1.41x).

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
  the bug fixes (20-b; 23-e, which fixes entry 24 on the way; the earlier
  one, 05-a, is upstream as #758), the features lean2rr needs (07-a,
  10-a, and entry 20's patches for step D), 21-a, an optimization with a
  large gain under `--int-backend rcgmp` (6 to 10% of the instructions of
  L12, L17 and Z01c), and entry 23's worklist drops, which bound the
  memory of deep frees (652 MB to 68 MB on `RtClosureChainFree`), with
  23-k to 23-m, which let lean2rr's runtime share entry 23's stack. A fix
  of a bug that lean2rr does not reach is parked (16-a, 19-a).
- A Reussir change is the last resort (owner): where lean2rr's runtime
  can do the work itself, it does, and the local patch goes (Phase 2:
  leanrt's own stack of pending releases replaced 02-a to 02-e and
  09-a). Entry 23 changes Reussir because the cost is in Reussir's own
  drop glue, which lean2rr's runtime does not run; with 23-k to 23-m
  leanrt keeps no second stack beside it.
- A patch that only buys a small run-time gain on a few programs is
  parked, not kept (01-a, 06-a with 06-b; 11-a until Phase 2). Costs
  whose removal would be a redesign (3, 4) and missed optimizations stay
  unpatched, with the reason in their file.
- Pull requests: after #758 (05-a, merged as `ea240b19`) none for the
  patches of this directory (owner, 2026-10-19). Since 2026-10-25 the
  owner's rule is: rcgmp-related Reussir fixes and optimizations may go
  upstream as pull requests of at most 300 changed lines each, one
  reviewable and actionable change per pull request; the other local
  patches stay in the series. Entry 20's patches and 21-a are prepared
  as pull request candidates, not opened.
- Patches are local: lean2rr's work does not push them. The "Upstream
  note" at the end of a patched entry is text for an upstream report.
  Reussir's maintainer asked that Reussir-side changes for lean2rr be
  made here first, as patches on lean2rr's tree; he takes them from this
  directory himself (2026-10-25). So a patched entry must be readable on
  its own: what each patch does, why lean2rr needs it, its tests and its
  evidence (entries 20, 21, 23 and 24 are written so).
- lean2rr's workarounds stay, so that lean2rr also works with an unpatched
  Reussir. The exceptions are the features lean2rr requires
  ([what lean2rr needs](#applying-the-patches)). The workarounds for
  entries that upstream `7954a367` fixed are listed in
  [`docs/implementation/reussir-workarounds/`](../docs/implementation/reussir-workarounds/README.md)
  as "removable after the move". lean2rr's builds use a later base
  (`00906e38`), so each can go, one change per workaround, with its test.

## Review

Each patch is reviewed adversarially: code review, differential fuzzing
against an independent reference evaluator, ASan builds (Miri for the
runtime patches), and lean2rr's runtime suite and corpus, in rounds
repeated until one finds nothing. The review notes are local notes,
outside this repository (column *Notes*: their names). The patches were
reviewed under their old names, on the old base (entry 20's patches
under their step D names, on `00906e38`; entry 23's on `l2r-base7`). The
rows of the patches that left with Phase 2 (02-a to 02-e, 09-a) are in
git history (commit `419a74d4`):

| Patch (old name) | Round | Notes | Result |
|---|---|---|---|
| 07-a (38-a) | review-anybox r1 | `review-anybox/r1` | no defect; the atomic case was added to the patch's test |
| 10-a (41-a) | mem-nat review, RV8 | `mem/nat/review/FINDINGS.txt`, `rv8/nat/FINDINGS.txt` | no defect (the optional hardening is in) |
| 20-a (R1) | step D review | `stepd-r12/review/r1`, `stepd-r12/review/r1b` | no bug in the final version |
| 20-b (R2) | step D review | `stepd-r12/review/r2` | no bug in the final version |
| 20-c (R2b) | step D review | `stepd-r12/review/r2b` | no bug in the final version |
| 20-d (R2c) | step D review | `stepd-r12/review/r2c` | no bug in the final version |
| 20-e (R3) | step D review | `stepd-r12/review/r3` | no bug in the final version |
| 21-a | independent review | `rccancel-review/` | sound; its three findings (test inputs, the crossed operations in the message with a negative test, the stop at `rcgmp.bridge.mpz.is_unique`) are in the patch |
| 23-a to 23-j | two adversarial rounds (runtime, IR and pipeline; glue, member kinds, release order and tests), then an independent re-review | `lifodrop-review/rt/NOTES.md`, `lifodrop-review/gen/NOTES.txt`, `lifodrop-review/gen/v2/` | round one: two order bugs (the tail call taken although a later member pushed; an anonymous recursive arm taken for a leaf), the TPDE token leak (entry 24), a flex box accepted by `rc.defer`, a defer outside a drain that waited for a later drain, a buffer leaked after the thread-exit guard, and documentation and test gaps: all fixed in the patches; re-review: the type predicates exponential on generated inputs (fixed: one reachability walk per query), nothing else; the fixes were checked with targeted lit tests and ASan |
| 23-k to 23-m | made and tested by the runtime side, then an adversarial review (2026-10-25) | `phase2/shared/` | its fixes are in the patches: a step is `extern "C"`, so a panicking step aborts instead of unwinding with the thread marked as draining; the nesting of end work requested inside the end function (one level per generation, as natively) and the entry costs of runs are documented; on the first version (`fbc2bba2`), leanrt's unit tests 101 of 101 (leanrt build) and 104 of 104 (rcgmp build) and the trace digests of 400 random order scenarios equal to those of leanrt's own stack |
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
`drop_stack.rs` and its tests (reviewed, 2026-10-25).

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
  own now.) 23-b declares the drop stack's two runtime functions
  `nounwind` only, since their callbacks run arbitrary drop glue.
- **TokenReuse's locality bonus is dead code (not a bug).** In
  `lib/Transformation/TokenReuse/TokenReuse.cpp`, function `heuristic`,
  the walk from a new cell's field back to the cell it was loaded from
  steps to `dispatch.getValue()` where the scrutinee (`getVariant()`) is
  meant, and the field list it starts from is read from the `rc.create`
  itself, so the list is always empty and the bonus never applies (a
  missed optimization; with only the first mistake corrected,
  `reussir-opt --reussir-token-reuse` crashes on a result-less dispatch).
  Not rechecked on `7954a367`; token reuse has no change up to
  `0378b744`. [Issue 8](08-alias-release-donor.md) is a
  case where the bonus would decide for the matched cell.

## Missing features that cost lean2rr performance

Not bugs, but each one costs lean2rr measurably:

- **Borrowed parameters.** Reads of arrays and strings through the runtime
  take the container owned, so each read retains and releases it.
  Traversals that keep unchanged nodes pay the same on fields (about 1.5x
  native on an `Expr.replace`-style DAG traversal). Reported upstream as
  issue #762 (open at `0378b744`).
- **A one-word `Nat`** (done locally: [issue 10](10-tagged-ffi-objects.md),
  patch 10-a, tagged opaque handles; `Nat` and `Int` are one tagged word,
  as natively).
- **`[value]` types across the FFI.** Arrays of enumerations or `[value]`
  records need runtime-side representations or wrappers.
- **Guaranteed tail calls.** Mutual tail calls are sibling calls only when
  all arguments fit in registers.
