# Workarounds for Reussir

Everything lean2rr does because of a Reussir issue: a bug, a cost or a
limitation. The open issues themselves (repro, cause, patch) are
documented one file each in [`reussir-bugs/`](../../../reussir-bugs/README.md), whose
column *Kind* says what each is: only a *bug* is erroneous behaviour;
costs, the missed optimizations (1, 6, 8, 17), the missing features (2, 7,
9, 10) and the dependency issue (15, in mimalloc) have correct
output, and their patches are optimizations or features, not fixes
([kinds](../../../reussir-bugs/README.md#kinds)). This directory says
what lean2rr does about them and whether the patched Reussir still needs
it. Policy
([`reussir-bugs/README.md`](../../../reussir-bugs/README.md#policy)):
lean2rr's workarounds stay even when a local patch fixes the bug or
improves the cost, so that lean2rr also works with an unpatched Reussir;
the exceptions are the patches for missing features that lean2rr
requires: 02-b (the runtime needs it to build), 02-a, 09-a, 07-a and
02-e (`scripts/l2r.py` checks for them) and 10-a (the prelude needs it); see
the table below.

- [correctness-bugs.md](correctness-bugs.md): workarounds for bugs that
  affected the program rather than its build time (wrong values, rrc
  crashes or rejected programs), all fixed upstream at Reussir
  `7954a367`, and the drain-end hook (patch 09-a). For issue 5,
  `scripts/l2r.py` passes `--relocation-mode pic` (patch 05-a makes it
  rrc's default for linked products; table below).
- [build-time.md](build-time.md): workarounds for a build-time bug and
  build-time costs, all fixed upstream at Reussir `7954a367`.
- [limitations.md](limitations.md): Reussir behaviour that is not a bug
  but shapes lean2rr's output: the 16-byte alignment of Rust allocations,
  a missed optimization (1), a missing feature (2), the FFI boundary,
  `unit`, tail calls, `str` arguments, syntax, the driver's flags.

## Summary

lean2rr's builds use upstream Reussir `7954a367` (2026-10-19) plus the
9 patches of the series: `./reussir`'s branch `l2r-base3` (head
`4c490260`). The base before it was `l2r-base2` (head `b2e4a47e`),
Reussir `943f2195` plus the 35 patches of the old series, whose files are
in git history and in that branch. The files in `reussir-bugs/` describe
the state at `7954a367`: it fixes 30 of the old entries in full, so
their files are gone and the open entries have new numbers (the mapping
is in [`reussir-bugs/README.md`](../../../reussir-bugs/README.md)). The
series there has 9 patches on `7954a367`: 02-a to 02-e (native release
order, issue 2), 09-a (the drain-end hook,
[issue 9](../../../reussir-bugs/09-drain-end-hook.md)), 10-a (tagged
opaque handles, [issue 10](../../../reussir-bugs/10-tagged-ffi-objects.md)),
05-a and 07-a. The owner keeps only bug fixes and major items in the
series: the optimizations 01-a (issue 1), 06-a and 06-b (issue 6) and
11-a (issue 11), and the fix 16-a
([issue 16](../../../reussir-bugs/16-driver-stack-address-limit.md), a
bug lean2rr does not reach), are parked, outside the series
([parked patches](../../../reussir-bugs/README.md#parked-patches)).

A workaround for an issue that Reussir `7954a367` fixes is marked
"removable after the move to Reussir 7954a367": lean2rr's builds use
that base, so it can go (one change per workaround, with its test).

Column "Needed with the patch?": whether lean2rr's workaround is still
needed once the patch is applied. By the policy above, workarounds stay
either way.

| Issue | Kind | lean2rr workaround | Local patch | Needed with the patch? |
|---|---|---|---|---|
| [1](../../../reussir-bugs/01-phantom-reuse-donor.md) | missed optimization | `lazy-fields`, `nullary-scrutinee`, `sink-proj` | none (01-a parked: `lazy-fields` covers it) | n/a; the passes are needed (the parked 01-a also missed the call-before-branch case) |
| [2](../../../reussir-bugs/02-native-drop-order.md) | missing feature (the stack depth is fixed upstream; native release order is not) | runtime frees through 02-b's stack | 02-a to 02-e | n/a: the runtime needs 02-b, and `scripts/l2r.py` requires 02-a and 02-e |
| [3](../../../reussir-bugs/03-value-record-dag.md) | cost | none (lean2rr's `[value]` records are shallow) | none (cost) | n/a |
| [4](../../../reussir-bugs/04-emit-mlir-size.md) | cost | none (affects `--emit mlir` only) | none (cost) | n/a |
| [5](../../../reussir-bugs/05-executable-textrel.md) | bug | `scripts/l2r.py` passes `--relocation-mode pic` (as native Lean, a PIE without text relocations) | 05-a | keep: harmless with 05-a, and needed without it |
| [6](../../../reussir-bugs/06-trampoline-inline.md) | missed optimization | read textures kept small (the view protocol, [ownership.md](../ownership.md#reads-give-their-reference-up-first-for-a-view)); three reads (a box; a `Nat` or `Int` element at its type) stay calls at a cold call site, which `tests/runtime/ffi-inline-check.sh` allows in `RtReadsDeep` only | none (06-a and 06-b parked: the gain is too small) | n/a |
| [7](../../../reussir-bugs/07-tagged-top-bits.md) | missing feature | none: the one-word `Box` keeps its payload's type number in the top 16 bits | 07-a | n/a: `scripts/l2r.py` requires it |
| [8](../../../reussir-bugs/08-alias-release-donor.md) | missed optimization | avoided: a field put back into a rebuilt node is boxed again from its unboxed value ([records.md](../representations/records.md#a-field-is-read-at-its-binders-type-once)); passing the field's own box (commit 3f0cb30, reverted) left a dead release of the unboxed value that token reuse preferred to the matched cell (`RtProbeBump`) | none (missed optimization) | n/a |
| [9](../../../reussir-bugs/09-drain-end-hook.md) | missing feature | none since switch step 6 ([correctness-bugs.md](correctness-bugs.md#the-drain-end-hook-local-patch-09-a)) | 09-a | n/a: `scripts/l2r.py` requires it |
| [10](../../../reussir-bugs/10-tagged-ffi-objects.md) | missing feature | none: `Nat` and `Int` are tagged handles ([nat-int.md](../representations/nat-int.md)) | 10-a | n/a: the prelude declares `Nat` and `Int` `tagged` |
| [15](../../../reussir-bugs/15-mimalloc-arena-purge.md) | issue (dependency: mimalloc v2.2.4) | leanrt sets mimalloc's `arena_purge_mult` to 0 on v2.1.8 to v2.2.7, so free arena memory goes back to the OS at once ([startup/entry.md](../startup/entry.md#free-arena-memory-goes-back-to-the-os-at-once-mimalloc-v218-to-v227)) | none (a newer `libmimalloc-sys`, 0.1.49 or later, parked) | n/a: with a fixed mimalloc the workaround turns itself off; delete it then |
| [17](../../../reussir-bugs/17-padded-member-widening.md) | missed optimization | a join point's tuple (J2) has its fields in decreasing alignment, as records have (`jpTupleOrder`, `field-order`; [join-points.md](../control-flow/join-points.md#a-j2-join-point-with-several-parameters-yields-a-value-tuple)) | none | n/a (no patch) |

Issues 11 to 14 and 16 (a cost of 02-b's stack; three bugs of Reussir's
runtime and hand-written MLIR; rrc's driver stack under an address-space
limit, which lean2rr's builds do not set) need nothing from lean2rr.

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
| 35 | cost | #690 | none; `scripts/l2r.py` sets `REUSSIR_FFI_CACHE_DIR`, which #690's cache also reads | keep the variable |

The other fixed issues (8, 9, 11, 12, 14, 15, 23, 24, 26 to 30, 33) had
no lean2rr workaround.
