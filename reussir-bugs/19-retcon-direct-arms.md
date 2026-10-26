# 19. Retcon destructors' direct arms are expanded in place at every drop site (reussir#759)

**Kind:** bug. rrc's drop expansion writes out the drop of a variant's
direct arms in place at every drop site, nested types included, so the
code grows exponentially with type nesting, and rrc runs out of memory
on valid programs of modest size (lean2rr's `RtSyncSelect`: above 10 GiB).
Patch 19-a drops the direct arms in one function per type. lean2rr no
longer reaches the bug: since 23-f rrc makes no retcon destructors
([issue 23](23-worklist-drops.md)), so 19-a is parked.

## Summary

**Kind:** bug (rrc runs out of memory on valid input: the code of a drop
is exponential in type nesting). **Status:** does not affect lean2rr
since 2026-10-25 (base `l2r-base10`): patch 23-f switches rrc's pipeline
from retcon destructors to worklist drops, so no retcon destructor and no
direct-arm expansion is made, and patch 19-a is parked
([`patches/parked/19-a-retcon-direct-arms.patch`](patches/parked/19-a-retcon-direct-arms.patch)).
19-a was made for Phase 2's first base, `l2r-base7` (commit `9b6f2915`),
which used upstream's retcon drops; `l2r-base10` replaced that base
before it reached lean2rr's dev branch. The bug stays reachable through
`reussir-opt`'s `retcon-drops` option.

**Upstream (2026-10-25):** Open at 00906e38: upstream issue #759 (ours,
with the measurements of the options below). Reussir's
maintainer chose option (a+), which is 19-a, and asked that it stay a
local patch. If the retcon lowering is deleted (entry 23's open items),
the bug goes with it.

Why this is a bug and entry [3](03-value-record-dag.md) is a cost: entry
3's exponential copy is deliberate and needs `[value]` records shared in
a DAG, which lean2rr does not make. Here ordinary types make rrc fail:
five nested enums of five arms each (the repro) take more than 12 GiB,
and lean2rr's closure enums with 150 and more arms more than 10 GiB.

## Context

- **Drop expansion.** Reussir's pass `AcquireDropExpansion`
  (`lib/Conversion/AcquireDropExpansion/AcquireDropExpansion.cpp`) turns
  each drop of a value into code: release the members, then free the
  cell.
- **Record drop kinds** (upstream #675 to #682;
  `RecordType::classifyRecordDrop`, `lib/IR/RecordDrop.cpp`). A type with
  no cycle is *Direct*; a type whose only recursive member is the last
  one is *TailLoop* (a loop); any other recursive type is *Worklist*: its
  destructor is a retcon coroutine. A drop of a recursive member suspends
  and yields the child to an executor (`crates/reussir-rt/src/dtor_executor.rs`),
  so the native stack stays bounded.
- **Direct arms.** A variant of a Worklist type whose members are not
  recursive (`d0(P, T0)` below) is a *direct arm*. Upstream drops a direct
  arm in place at the drop site, with no coroutine, which is fast for
  small values.
- **lean2rr.** Its closure types are enums with one arm per closure kind
  (up to hundreds of arms), recursive through the arms that capture
  closures, with many direct arms. Until 2026-10-25, lean2rr's builds had
  the local patch 02-a, which turned upstream's tail-recursive and retcon
  drops off ([issue 2](02-native-drop-order.md)), so they did not meet
  this bug. Phase 2's first base (`l2r-base7`) used upstream's drop
  design, retcon drops included, and needed 19-a; `l2r-base10` frees
  Worklist types through 23's worklist instead.

## Symptom and repro

Repro [`repros/bug19-retcon-direct-arms.py`](repros/bug19-retcon-direct-arms.py)
writes N nested enums, `T(k) = two(T(k), T(k)) | d0..d3(P, T(k-1))`,
and a function that drops one `T(N-1)` (the issue's `nest-N`).

**Command.** `rrc OUT.rr --emit mlir-llvm -O none -o OUT.mlir` for N = 3
and N = 4. `run.sh` compares the two sizes.

**Expected.** About the same growth for each level.

**Actual on upstream** (7954a367 with patches that do not touch drops;
lines of the LLVM-dialect module, checked again on 2026-10-25): N = 3
25,144, N = 4 97,090 (3.9 times for one level). As objects (`--emit
obj`): N = 4 1.65 GiB of rrc memory, N = 5 out of memory above 12 GiB.
With 19-a: 6,753 and 9,548 lines (1.4 times); N = 5 in about 110 MB.
`run.sh` printed `issue 19   FIXED       --emit mlir-llvm: N = 3: 322 KB,
N = 4: 457 KB (1.41x for one more level)` on `l2r-base7`. On 00906e38
(2026-10-25) it prints `REPRODUCES` (1167 KB and 4599 KB, 3.93x); on
`l2r-base9`, without 19-a, `FIXED` (59 KB and 69 KB, 1.16x), because rrc
makes no retcon destructor there.

## Cause

A drop of a Worklist variant with direct arms is expanded at the drop
site into a dispatch on the tag: a direct arm's member drops are written
in place, and a member of another Worklist type with direct arms is
expanded the same way, with no outlining and no size limit. One site
holds the whole unfolded tree of direct-arm drops: 4 direct arms per
level give about 4 times the code per level of nesting. Inside a retcon
destructor, each drop site also dispatches over every arm of the type
(`record.dispatch` lowers to one block per tag), and LLVM's CoroSplit
copies that into every resume clone, so a type with many arms costs
arms x sites there.

## Patch

Parked patch file
[`patches/parked/19-a-retcon-direct-arms.patch`](patches/parked/19-a-retcon-direct-arms.patch)
(commit `9b6f2915` on `l2r-base7`; option (a+) of the issue, measured as
"a+m2" in our notes). It applies to `00906e38` and to `l2r-base10`
(`git apply --check`, 2026-10-25). The direct-arm path is emitted once per type, as
`<dtor>.direct`: a plain (not coroutine) `linkonce_odr` function that
dispatches on the tag, drops a direct arm in place one level deep (a
nested type's drop is a call to its own `.direct` or destructor) and
calls the retcon destructor for every other arm.

- A drop site outside a retcon destructor calls `<dtor>.direct`.
- A drop site inside a retcon destructor tests the tag once against a
  constant mask, `(MASK >> tag) & 1`: a set bit calls `<dtor>.direct`, a
  clear bit suspends into the running executor (`reussir.dtor.suspend`),
  as before. MASK has the direct arms whose drop cannot run a retcon
  destructor (a memoized walk over the member types). A direct arm that
  holds a retcon value suspends too, so that value is dropped in the
  running executor and does not start its own. The site is O(1) in the
  number of arms.

Upstream #800's load forwarding runs after the expansion as before, on
every function including the `.direct` ones.

**Tests.** `conversion/retcon_drop_leaf.mlir` checks the new shapes (the
`.direct` function, the call at a root site, the masked test inside a
retcon destructor); `conversion/retcon_drop_direct_nested.mlir` checks
that a nested retcon type's drop inside `.direct` is a call to that
type's `.direct` (no copy of its arms) and that a direct arm holding a
retcon value is not in the mask. On `l2r-base7` (2026-10-25, notes in
`reussir-move/base7/`): Reussir's lit tests 767 passed, 125 unsupported
and 2 failed (`frontend/kernel_launch_disabled.rr` and
`kernel_launch_config_errors.rr`: the test environment has no `not`
tool); Reussir's C++ unit tests (`reussir-ut`) 82 of 82. In the issue's
measurements (on 7954a367), Reussir's 66 lit tests that touch drops
passed for every option.

**Measured** (rrc's peak memory, lean2rr's rrc flags, `--emit obj`, `-O
aggressive`):

| Input | upstream | with 19-a (`l2r-base7`) |
|---|---|---|
| `RtSyncSelect`, the issue's input (closure enums of 151 and 177 arms) | out of memory above 10 GiB | 1.49 GB, 41 s |
| Z01c (the bench set's compressor), the issue's input | 8.21 GiB, 363 s | 4.62 GB, 130 s |
| `RtSyncSelect`, lean2rr's current output | - | 1.96 GB, 60 s |
| Z01c, lean2rr's current output | - | 0.70 GB, 26 s |

The upstream column is from the issue's measurements on 7954a367 (with
patches that do not touch drops). Z01c's 4.6 GB is the level that the
issue gives for Reussir before 7954a367, which had no retcon drops.

**Run time of drops** (cachegrind instructions against upstream, in the
issue's measurements on 7954a367; the option's prototype): -0.9% to
+0.14% on a binary tree, a tail-loop list of small trees, a 33-arm
value in a holder, and a red-black tree; +7.2% in the worst case built
for it (a retcon value inside a direct arm, dropped from a retcon
destructor; the plain option (a) gave +19% there). Peak memory and the
checksums are the same as upstream's.

**Other options** (issue #759; the full tables are in the issue): (a),
one `.direct` function without the mask, removes the exponential growth
but keeps the per-site dispatch inside retcon destructors
(`RtSyncSelect` 4.42 GiB); (b), a call per arm at each site, 10.70 GiB;
(c), a size budget per function, bounds the size (1.62 GiB) but a site
past the budget loses the in-place path (up to +44% on small values).

**Effect on lean2rr.** With upstream's retcon drops on (`l2r-base7`),
`RtSyncSelect` and Z01c compiled in bounded memory only with the patch.
On `l2r-base9`, without 19-a, rrc compiles `RtSyncSelect` in 1.94 GB and
57 s and `RtDepPolyRec` in 3.47 GB and 109 s (lean2rr's flags, `--emit
obj`, 2026-10-25), as with 19-a and worklist drops on `l2r-base7` (1.95
GB, 3.43 GB).

## Upstream note

Reported as reussir-lang/reussir#759, with the options and their
measurements; the maintainer chose (a+), this patch, and asked that it
stay a local patch here.
