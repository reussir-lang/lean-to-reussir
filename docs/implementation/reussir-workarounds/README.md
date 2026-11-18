# Workarounds for Reussir

Everything lean2rr does because of a Reussir issue: a bug, a cost or a
limitation. The open issues themselves (repro, cause, patch) are
documented one file each in [`reussir-bugs/`](../../../reussir-bugs/README.md), whose
column *Kind* says what each is: only a *bug* is erroneous behaviour;
costs, the missed optimizations (1, 6, 8, 17, 18, 21), the missing
features (2, 7, 10, 20), the dependency issue (15, in mimalloc) and the
sharp edge (25, the texture cache's key) have correct
output, and their patches are optimizations or features, not fixes
([kinds](../../../reussir-bugs/README.md#kinds)). This directory says
what lean2rr does about them and whether the patched Reussir still needs
it. Policy
([`reussir-bugs/README.md`](../../../reussir-bugs/README.md#policy)):
lean2rr's workarounds stay even when a local patch fixes the bug or
improves the cost, so that lean2rr also works with an unpatched Reussir;
the exceptions are the patches that lean2rr requires, all for missing
features: 10-a (the prelude needs it), 07-a, 20-a, 20-c and 20-d, and
two fixes of upstream bugs, 26-a and 28-a
(`scripts/l2r.py` checks for each: `REQUIRED_REUSSIR_PATCHES`,
`RCGMP_REUSSIR_PATCHES`). The driver also requires upstream's scoped
drop worklists (`join_or_run_step`, `defer_until_scope_exit`), which
leanrt's pending work needs to compile: that is upstream code, not a
patch, and it refuses an older base. See the table below.

- [correctness-bugs.md](correctness-bugs.md): workarounds for bugs that
  affected the program rather than its build time (wrong values, rrc
  crashes or rejected programs), all fixed upstream at Reussir
  `7954a367`. For issue 5 (fixed upstream at `ea240b19`, number
  retired), `scripts/l2r.py` still passes `--relocation-mode pic` (below
  the table).
- [build-time.md](build-time.md): workarounds for a build-time bug and
  build-time costs, all fixed upstream at Reussir `7954a367`, and one
  current cost with no entry in `reussir-bugs/`: the inliner copies a
  callee into every call of one function (lean2rr's copy anchors,
  required practice `inline-anchors`).
- [limitations.md](limitations.md): Reussir behaviour that is not a bug
  but shapes lean2rr's output: the 16-byte alignment of Rust allocations,
  a missed optimization (1), a missing feature (2), the FFI boundary,
  `unit`, tail calls, `str` arguments, syntax, the driver's flags.

## Summary

lean2rr's builds use upstream Reussir `36a55a0f` (2026-11-17) plus the
12 patches of the series (the Reussir branch `l2r-base13-final`, head
`d62797ac`; [`reussir-bugs/patches/base`](../../../reussir-bugs/patches/base)
holds the upstream commit): 10-a (tagged opaque handles,
[issue 10](../../../reussir-bugs/10-tagged-ffi-objects.md)), 07-a,
20-a, 20-g, 20-c, 20-d and 20-e (the interface for `Nat` and `Int` on
rcgmp, [issue 20](../../../reussir-bugs/20-rcgmp-integration.md), for
step D), 21-a
([issue 21](../../../reussir-bugs/21-value-record-member-retains.md)),
29-a ([issue 29](../../../reussir-bugs/29-texture-store-open.md)),
and the fixes of three upstream bugs that the port found: 26-a
([issue 26](../../../reussir-bugs/26-trmc-observable-release.md)), 27-a
([issue 27](../../../reussir-bugs/27-is-unique-tbi-immediate.md)) and
28-a ([issue 28](../../../reussir-bugs/28-sve-vector-storage.md)).
The move to this base
([history](../../../reussir-bugs/README.md#history-the-move-to-36a55a0f-2026-11-17))
changed these things for lean2rr:

- **Worklist drops are upstream's.** Upstream took the design of
  [issue 23](../../../reussir-bugs/23-worklist-drops.md) on 2026-11-01:
  rrc frees the records of a recursive type through scoped drop
  worklists, and the retcon coroutines are deleted. The sixteen patches
  23-a to 23-p are parked as history. leanrt keeps its pending releases
  on upstream's drop scopes
  ([ownership.md](../ownership.md#runtime-objects-free-through-leanrts-pending-stack-in-leans-order)).
- **The drop order is a flag, and two of its rules are new.**
  `scripts/l2r.py` passes `--drop-order backward`. A whole value is one
  free, last field first; a drop run that starts inside a free finishes
  first. lean2rr's emitter has two rules for them: the known-constructor
  release and the payload release that joins the free
  ([limitations.md](limitations.md#reussirs-drop-order-is-not-native-leans-in-every-case-issue-2-missing-feature)).
- **The texture cache has a new key.** rrc keys it on paths, so the
  driver names the runtime build in the path of the rustc that it gives
  rrc, and keeps the cache in lean2rr's directory
  ([issue 25](../../../reussir-bugs/25-texture-cache-key.md);
  [build-time.md](build-time.md#old-issue-35-cost-every-texture-was-compiled-again-on-every-build)).
- **Borrowed parameters.** rrc has a borrow analysis, on by default.
  lean2rr passes no flag for it; its own emulation of Lean's borrowed
  parameters stays as it is.
- **TRMC keeps a self call in place across a call.** So lean2rr binds
  the boxes of a constructor before the self call whose result the
  constructor takes, and its list and tree maps are loops again
  ([../control-flow/calls-and-lets.md](../control-flow/calls-and-lets.md)).
- **A large function can fail to compile on a host with SVE** without
  28-a (issue 28). lean2rr has no workaround; the series has the fix.
- **Out of the series:** 20-b (tests only).

Verified on the new base: the port's final gate (2026-11-18, lean2rr
`8d032fdb` on the series): 748 of 750 runtime tests identical to
native with 2 expected failures, 23 of 23 check scripts, the classic
corpus in its three modes, the raytracer
([`reussir-bugs/README.md`](../../../reussir-bugs/README.md) has the
results). Not verified there: every "kept: measured ..." line of this
directory (the measurements are of the earlier bases), and wall time
(pending the timing run).

The base before this one was `l2r-base12` (head `c1170ff9`): upstream
`95d9a1c8` (2026-10-26) plus 24 patches, with 20-b's tests, 20-e, 21-a
and 23-a to 23-p in the series. It had none of the old drop patches.
The bases before it had 6 more patches: five for native release order
through a pending stack shared with leanrt (02-a to 02-e, issue 2), and
a drain-end hook (09-a, issue 9, now retired); leanrt's own pending
stack replaced them. Phase 2's first base, `l2r-base7` (head
`bfe3d32d`), used upstream's retcon drops and needed 19-a (issue 19,
reussir#759: the drop expansion's code grew exponentially with type
nesting); with 23-f rrc made no retcon destructors, so 19-a was parked
(upstream has deleted the retcon drops since).
The last base before Phase 2 was upstream `00906e38` plus 14 patches:
`./reussir`'s branch `l2r-base8` (head `8e9a6293`, `l2r-stepd` plus
21-a), step D's 5 patches (issue 20) after the 8 of the stack
`l2r-base5` (head `c4a5df4b`), then 21-a. Upstream `00906e38` (#804)
only moves the commit of mlir-rcgmp that Reussir's build fetches; the
move to it changed no issue and no workaround. Before it, `l2r-base5`
was upstream `ea240b19` plus the same 8 patches (head `e1680f65`), and
until the move to `ea240b19` (2026-10-25), upstream `0378b744`
(2026-10-24) plus 9 patches (head `6bf9be85`); upstream `ea240b19` is
our pull request #758, the change of patch 05-a, so the move dropped
05-a, deleted issue 5 (its number is retired) and needed no change of a
workaround. The base before `0378b744` was `l2r-base3` (head
`4c490260`): upstream `7954a367` (2026-10-19) plus the same 9 patches;
the move to `0378b744` fixed no open issue and needed no change of a
workaround. Before that it was `l2r-base2` (head `b2e4a47e`), Reussir
`943f2195` plus the 35 patches of the old series, whose files are in git
history and in that branch. The files in `reussir-bugs/` describe the
state at `36a55a0f` where they were checked there, and say so where they
were not: `7954a367` fixed 30 of the old entries in full, so
their files are gone and the open entries have new numbers (the mapping
is in [`reussir-bugs/README.md`](../../../reussir-bugs/README.md)). The
owner keeps only bug fixes and major items in the series: the
optimizations 01-a (issue 1), 06-a and 06-b (issue 6), and the fixes
16-a ([issue 16](../../../reussir-bugs/16-driver-stack-address-limit.md))
and 19-a ([issue 19](../../../reussir-bugs/19-retcon-direct-arms.md);
fixed upstream now), bugs lean2rr does not reach, are parked, outside the series
([parked patches](../../../reussir-bugs/README.md#parked-patches)).

A workaround for an issue that Reussir `7954a367` fixes is marked
"removable after the move to Reussir 7954a367": lean2rr's builds use a
later base (`36a55a0f`), so it can go (one change per workaround, with
its test).

Column "Needed with the patch?": whether lean2rr's workaround is still
needed once the patch is applied. By the policy above, workarounds stay
either way.

| Issue | Kind | lean2rr workaround | Local patch | Needed with the patch? |
|---|---|---|---|---|
| [1](../../../reussir-bugs/01-phantom-reuse-donor.md) | missed optimization | `lazy-fields`, `nullary-scrutinee`, `sink-proj` | none (01-a parked: `lazy-fields` covers it) | n/a; the passes are needed (the parked 01-a also missed the call-before-branch case) |
| [2](../../../reussir-bugs/02-native-drop-order.md) | missing feature (the stack depth is fixed upstream; the order is a flag, and native Lean's exact rule is not one of its values) | `scripts/l2r.py` passes `--drop-order backward`; leanrt keeps its pending releases on Reussir's drop scopes: native order inside every free that starts at a runtime object. Where lean2rr releases a value itself, it gives native's order: one free from the root, or field by field where Lean knows the constructor (`l2r_release_known_<type>`); a box's payload release joins the running free (`payloadJoins`). Left: a matched value that Reussir consumes in its `match`, a reset value, a value shared by two fields (plan §10; [ownership.md](../ownership.md#runtime-objects-free-through-leanrts-pending-stack-in-leans-order), [limitations.md](limitations.md#reussirs-drop-order-is-not-native-leans-in-every-case-issue-2-missing-feature)) | none (the five patches 02-a to 02-e went with leanrt's own stack) | n/a |
| [3](../../../reussir-bugs/03-value-record-dag.md) | cost | none (lean2rr's `[value]` records are shallow) | none (cost) | n/a |
| [4](../../../reussir-bugs/04-emit-mlir-size.md) | cost | none (affects `--emit mlir` only) | none (cost) | n/a |
| [6](../../../reussir-bugs/06-trampoline-inline.md) | missed optimization | read textures kept small (the view protocol, [ownership.md](../ownership.md#reads-give-their-reference-up-first-for-a-view)); the reads of a box and of a `Nat` or `Int` element (at its type, or from a typed array) stay calls at a cold call site, which `tests/runtime/ffi-inline-check.sh` allows in `RtReadsDeep` only | none (06-a and 06-b parked: the gain is too small) | n/a |
| [7](../../../reussir-bugs/07-tagged-top-bits.md) | missing feature | none: the one-word `Box` keeps its payload's type number in the top 16 bits | 07-a | n/a: `scripts/l2r.py` requires it |
| [8](../../../reussir-bugs/08-alias-release-donor.md) | missed optimization | avoided: a field put back into a rebuilt node is boxed again from its unboxed value ([records.md](../representations/records.md#a-field-is-read-at-its-binders-type-once)); passing the field's own box (commit 3f0cb30, reverted) left a dead release of the unboxed value that token reuse preferred to the matched cell (`RtProbeBump`) | none (missed optimization) | n/a |
| [10](../../../reussir-bugs/10-tagged-ffi-objects.md) | missing feature | none: the box `LAny` is a tagged handle ([box-and-uniform.md](../representations/box-and-uniform.md); until D8 also `Nat` and `Int`, [nat-int.md](../representations/nat-int.md)) | 10-a (on `36a55a0f` also the rule at upstream's worklist drops and at `core::object::is_unique`) | n/a: the prelude declares `LAny` `tagged`, and `scripts/l2r.py` checks for the worklist rule |
| [15](../../../reussir-bugs/15-mimalloc-arena-purge.md) | issue (dependency: mimalloc v2.2.4) | leanrt sets mimalloc's `arena_purge_mult` to 0 on v2.1.8 to v2.2.7, so free arena memory goes back to the OS at once ([startup/entry.md](../startup/entry.md#free-arena-memory-goes-back-to-the-os-at-once-mimalloc-v218-to-v227)) | none (a newer `libmimalloc-sys`, 0.1.49 or later, parked) | n/a: with a fixed mimalloc the workaround turns itself off; delete it then |
| [17](../../../reussir-bugs/17-padded-member-widening.md) | missed optimization | every generated tuple (a join point's, J2; a `flatten-structs` result) has its fields in decreasing alignment, as records have (`memberOrder`, `field-order`; [records.md](../representations/records.md#fields-are-ordered-by-decreasing-alignment)) | none | n/a (no patch) |
| [18](../../../reussir-bugs/18-tail-padding-return.md) | missed optimization | the tuple of a `flatten-structs` result keeps a `bool`, `u8`, `u16` or `u32` in a `u64` member and has no member for a unit value, so it has no tail padding (`tupleMemberTy`; [records.md](../representations/records.md#fields-are-ordered-by-decreasing-alignment)) | none | n/a (no patch) |
| [19](../../../reussir-bugs/19-retcon-direct-arms.md) | bug (rrc's memory, reussir#759); fixed upstream, to delete | none needed (on `l2r-base7` rrc ran out of memory on `RtSyncSelect` without 19-a) | none (19-a parked, history) | n/a |
| [20](../../../reussir-bugs/20-rcgmp-integration.md) | missing feature (20-b's fix of a bug is upstream) | none: lean2rr's step D (on dev since `1e57ed53`, 2026-10-25; the only representation of `Nat` and `Int` since D8, 2026-10-26) uses the interface the patches add | 20-a, 20-g, 20-c, 20-d, 20-e (parked: 20-b, tests) | n/a: every build needs 20-a and upstream's `Mpz` (`check_rcgmp`), and `scripts/l2r.py` checks for 20-c and 20-d; 20-g and 20-e are optimizations that nothing requires (without 20-e a `Nat` literal of 100,000 digits takes rrc about 19 minutes) |
| [21](../../../reussir-bugs/21-value-record-member-retains.md) | missed optimization | none: the pairs stay without the patch | 21-a (reworked for `36a55a0f`) | n/a: an optimization; nothing requires it |
| [23](../../../reussir-bugs/23-worklist-drops.md) | cost (memory and run time of frees); fixed upstream (scoped worklists, 2026-11-01), to delete | none: leanrt's pending work is built on upstream's drop scopes. `RtDeepTreeFree`, `RtClosureChainFree`, `RtAltTreeFree` and `RtArrayPileFree` keep their alloc-check bounds on the new base (the port's first gate) | none (23-a to 23-p parked, history) | n/a: `scripts/l2r.py` requires upstream's `join_or_run_step` and `defer_until_scope_exit` |
| [25](../../../reussir-bugs/25-texture-cache-key.md) | sharp edge (a documented rule) | `scripts/l2r.py` gives rrc a rustc script whose path names the build of leanrt, of lean-runtime and of Reussir's runtime, and sets `XDG_CACHE_HOME` for rrc to `L2R_POLYFFI_CACHE` ([build-time.md](build-time.md#old-issue-35-cost-every-texture-was-compiled-again-on-every-build)); test `tests/runtime/texture-cache-check.sh` | none | n/a (no patch) |
| [29](../../../reussir-bugs/29-texture-store-open.md) | cost (build time: rrc opened its texture store once for each texture) | none in the driver; `L2R_POLYFFI_CACHE` can name a directory on a memory file system, which removes the sync cost (the port's final gate did so) | 29-a | n/a: an optimization; nothing requires it |
| [26](../../../reussir-bugs/26-trmc-observable-release.md) | bug (TRMC moves a self call before a release with a foreign cleanup) | none: lean2rr's own releases are calls, which keep the self call in place; no lean2rr program is known to reach the bug | 26-a | no workaround to keep; `scripts/l2r.py` requires the patch |
| [27](../../../reussir-bugs/27-is-unique-tbi-immediate.md) | bug (aarch64 with TBI: `is_unique` true for an immediate) | none: lean2rr does not call the intrinsic | 27-a | no workaround to keep |
| [28](../../../reussir-bugs/28-sve-vector-storage.md) | bug (aarch64 with SVE: rrc fails on a large function without vectors) | none in lean2rr | 28-a | n/a: `scripts/l2r.py` requires the patch; without it the row oracle of `rows-check.sh` does not build on a host with SVE |

Issues 12 to 14, 16 and 24 (three bugs of Reussir's runtime and
hand-written MLIR; rrc's driver stack under an address-space limit,
which lean2rr's builds do not set; a leak with TPDE's drop options,
which rrc's command line cannot select, fixed upstream at `36a55a0f`
and to delete) need nothing from lean2rr. Issues 9 and 11 (the drain-end hook and the cost of a one-cell
free on the old shared stack) were retired with Phase 2: lean2rr no
longer uses that stack, and leanrt's outermost free runs the end work
itself.

Issue 5 (a bug: `rrc --emit executable` compiled static code but linked
a PIE, so the executable had text relocations with GNU ld, and lld
refused to link it) is fixed upstream in full by #758
(`ea240b19`, the change of the local patch 05-a). Its file and its patch
are deleted (in git history, commit `0f9e1b05`), and number 5 is
retired. lean2rr's workaround stays: `scripts/l2r.py` passes
`--relocation-mode pic`, so the executable is a PIE without text
relocations, as native Lean's is. On `ea240b19` and later this is rrc's
default for executables, so the flag is redundant but harmless; it stays
for older bases. `tests/runtime/run.sh` fails a test whose executable
has text relocations.

The workarounds for issues that Reussir `7954a367` fixes (old entry
numbers; the details are in [correctness-bugs.md](correctness-bugs.md),
[build-time.md](build-time.md) and [limitations.md](limitations.md)):

| Old issue | Kind | Fixed upstream in Reussir | lean2rr workaround | Status |
|---|---|---|---|---|
| 1 | bug | #663 | none since 2026-10-19 (it was: only field-less `[value]` enums, and step enums whose representative arm carries the other arms' bytes); step enums, and `state-machines` entry enums with a kept field, are `[value]` | removed |
| 2 | bug | #652 (structures), #656 (variants) | `--no-pack-record-members`; fields ordered by alignment | the flag: removable after the move to Reussir 7954a367; `field-order` stays (records without padding) |
| 3 | cost (the 16-byte alignment is intended) | #667 | runtime allocates its objects with `mi_malloc` | kept: the runtime's objects need only 8-byte alignment, and its blocks stay smaller |
| 4 | bug | #654 | driver retries rrc without `--reuse-across-call` | kept as a fallback for unknown crashes |
| 5 | bug | #655 | runtime diagnostics through a C trampoline | removable after the move to Reussir 7954a367 (cheap; may stay) |
| 6 | bug | #661 | none; the runtime skips immediates when it frees or copies arrays of records | the skips stay: #661 keeps immediates from being freed |
| 10 | cost | #668 | `--no-closure-wpd` | removed: the executables of the large benchmark programs are byte-identical with and without it, at the same rrc time and memory ([build-time.md](build-time.md#old-issue-10-cost-closure-devirtualization-printed-types-exponentially)) |
| 16, 17 | costs | #672, #670 | `Outline` | removable after the move to Reussir 7954a367 as a workaround; kept for now (it also bounds the `.rr` text) |
| 18 | bug (build system) | #684 | build Reussir's default target | removable after the move to Reussir 7954a367 |
| 19 | bug | #666, #681 | no `[value]` record in a cell: references hold a `Box`, once-cells an `ElemBox` | removable after the move to Reussir 7954a367 |
| 20 | cost | #674 | `#[transform_anchor]` on conversion code | kept: measured again on Reussir 7954a367, the monad-transformer towers take 2.2 to 4 times the rrc time and 2 to 2.9 times the memory without the anchors ([build-time.md](build-time.md#old-issue-20-cost-the-inliner-multiplies-conversion-code)) |
| 21 | bug | #657 | `[` escaped in the string literal table | removable after the move to Reussir 7954a367 (free; may stay) |
| 22 | cost | #673 | `l2r_sink` in wildcard arms | removed: instruction counts unchanged, `.text` up to 0.7% larger on programs with wide enums ([build-time.md](build-time.md#old-issue-22-cost-a-wildcard-arm-over-a-wide-enum-cost-n3-code)) |
| 31 (partly: see [issue 16](../../../reussir-bugs/16-driver-stack-address-limit.md)) | bug | #686 (the stack overflow; the rest is issue 16) | `Outline` bounds nesting | removable after the move to Reussir 7954a367 (see old 16, 17) with #686's code; if the parked fix 16-a (or its upstream form) lands, rrc under a finite `ulimit -v` runs on the 8 MiB main thread again, and the bound is needed again |
| 35 | cost | #690, replaced by #852 (a store for each user, always on) | `scripts/l2r.py` sets `XDG_CACHE_HOME` for rrc (`L2R_POLYFFI_CACHE`) and names the runtime build in the rustc script's path ([issue 25](../../../reussir-bugs/25-texture-cache-key.md)); `REUSSIR_FFI_CACHE_DIR` is gone | kept: needed for correct builds after a runtime rebuild |

The other fixed issues (8, 9, 11, 12, 14, 15, 23, 24, 26 to 30, 33) had
no lean2rr workaround.
