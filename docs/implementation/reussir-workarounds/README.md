# Workarounds for Reussir

Everything lean2rr does because of a Reussir issue: a bug, a cost or a
limitation. The issues themselves (repro, cause, patch) are documented
one file each in [`reussir-bugs/`](../../../reussir-bugs/README.md), whose
column *Kind* says what each is: only a *bug* is erroneous behaviour;
costs, the missed optimizations (7, 36, 39), the missing features (13,
27, 38, 40, 41) and the dependency issue (46, in mimalloc) have correct
output, and their patches are optimizations or features, not fixes
([kinds](../../../reussir-bugs/README.md#kinds)). This directory says
what lean2rr does about them and whether the patched Reussir still needs
it. Policy
([`reussir-bugs/README.md`](../../../reussir-bugs/README.md#policy)):
lean2rr's workarounds stay even when a local patch fixes the bug or
improves the cost, so that lean2rr also works with an unpatched Reussir;
the exceptions are the patches for missing features that lean2rr
requires: 13-b (the runtime needs it to build), 40-a, 38-a and 13-d
(`scripts/l2r.py` checks for them) and 41-a (the prelude needs it); see
the table below.

- [correctness-bugs.md](correctness-bugs.md): bugs that affect the
  program rather than its build time: wrong values, rrc crashes or
  rejected programs, use after free (1, 2, 4, 5, 6, 8, 9/14, 12, 15, 19,
  21), and the drain-end hook (patch 40-a). Entries 24 to 33 need nothing
  from lean2rr; for 34, `scripts/l2r.py` passes `--relocation-mode pic`
  (patch 34-a makes it rrc's default for linked products; table below).
- [build-time.md](build-time.md): a build-time bug (18) and build-time
  costs (10, 11, 16, 17, 20, 22, 23, 35).
- [limitations.md](limitations.md): Reussir behaviour that is not a bug
  but shapes lean2rr's output: intended behaviour (3), a missed
  optimization (7), a missing feature (13), the FFI boundary, `unit`, tail
  calls, `str` arguments, syntax, the driver's flags.

## Summary

`l2r-base2` (head `71f17ae2`, since 2026-10-07) is the branch of
`./reussir` with the applied local patches: `943f2195`, a commit of
Reussir's `main`, plus the 35 patches of the series (the series and how
to apply it are in
[`reussir-bugs/README.md`](../../../reussir-bugs/README.md#applying-the-patches)).
The base has five of lean2rr's bug fixes, merged upstream (pull requests
#651 to #655: 26-a, 02-a, 09-a, 04-a and 05-a), so the series no longer
has them.
They include 40-a (the drain-end hook,
[issue 40](../../../reussir-bugs/40-drain-end-hook.md)), 41-a (tagged
opaque handles, [issue 41](../../../reussir-bugs/41-tagged-ffi-objects.md))
and 38-a and 13-d, features that `scripts/l2r.py` requires. The owner
keeps only bug fixes and major items in the series: the optimizations
07-a (issue 7) and 36-a and 36-b (issue 36) are parked, outside the
series ([parked patches](../../../reussir-bugs/README.md#parked-patches)).
`l2r-trim` (head `79c1d5f2`) is the series before the base moved:
`ef922049` plus 40 patches. `l2r-local` (head `136d9a9f`) is the series
before that, parked patches included.

Column "Needed with the patch?": whether lean2rr's workaround is still
needed once the patch is applied. By the policy above, workarounds stay
either way.

| Issue | Kind | lean2rr workaround | Local patch | Needed with the patch? |
|---|---|---|---|---|
| [1](../../../reussir-bugs/01-value-enum-payload.md) | bug | only field-less `[value]` enums (`Nat`/`Int` are tagged handles, 41-a) | 01-a, applied | no; kept (policy) |
| [2](../../../reussir-bugs/02-reuse-field-store.md) | bug | `--no-pack-record-members`; fields ordered by alignment | structures: fixed upstream (#652, in the base; 02-a dropped); variants: 02-b, applied | no; kept (policy) |
| [3](../../../reussir-bugs/03-global-alloc-align.md) | cost (the 16-byte alignment is intended) | runtime allocates its objects with `mi_malloc` | 03-a and 03-b, applied | kept: the runtime's objects need only 8-byte alignment, and its blocks stay smaller |
| [4](../../../reussir-bugs/04-recursive-type-compare.md) | bug | driver retries rrc without `--reuse-across-call` | fixed upstream (#654, in the base; 04-a dropped) | no; kept as a fallback for unknown crashes |
| [5](../../../reussir-bugs/05-one-armed-if.md) | bug | runtime diagnostics through a C trampoline | fixed upstream (#655, the base; 05-a dropped) | no; kept (policy) |
| [6](../../../reussir-bugs/06-static-count-wrap.md) | bug | none (flag alternative not used) | 06-a, applied | n/a |
| [7](../../../reussir-bugs/07-phantom-reuse-donor.md) | missed optimization | `lazy-fields`, `nullary-scrutinee`, `sink-proj` | none (07-a parked: `lazy-fields` covers it) | n/a; the passes are needed (the parked 07-a also missed the call-before-branch case) |
| [8](../../../reussir-bugs/08-padding-lift.md) | bug | shape never emitted | 08-a, applied | n/a |
| [9](../../../reussir-bugs/09-duplicate-bound-member.md), [14](../../../reussir-bugs/14-member-consumed-before-release.md) | bugs | none possible | fixed upstream (#653, in the base; 09-a dropped) | n/a |
| [10](../../../reussir-bugs/10-closure-type-print.md) | cost | `--no-closure-wpd` | 10-a, applied | no; kept (policy) |
| [11](../../../reussir-bugs/11-sccp-call-graph.md) | cost (11b too) | none | 11-a (and 11-b for 11b), applied | n/a |
| [12](../../../reussir-bugs/12-node-cache-collision.md) | bug | none possible | 12-a, applied | n/a |
| [13](../../../reussir-bugs/13-long-list-drop.md) | missing feature | runtime frees through 13-b's stack | 13-a to 13-d, applied | n/a: the runtime needs 13-b, and `scripts/l2r.py` requires 13-d |
| [15](../../../reussir-bugs/15-nullable-match-yield.md) | bug | `Nullable` not used | 15-a, applied | n/a |
| [16](../../../reussir-bugs/16-nested-io-matches.md), [17](../../../reussir-bugs/17-long-nat-block.md) | costs | `Outline` | 16-a and 17-a, applied | no; kept (policy, and it bounds the `.rr` text) |
| [18](../../../reussir-bugs/18-rrc-target-deps.md) | bug (build system) | build Reussir's default target | 18-a, applied | no |
| [19](../../../reussir-bugs/19-cell-of-value-record.md) | bug | no `[value]` record in a cell: references hold a `Box`, once-cells an `ElemBox` (`Nat`/`Int` are tagged handles, 41-a) | 19-a, applied | no; kept (policy) |
| [20](../../../reussir-bugs/20-statet-tower.md) | cost | `#[transform_anchor]` on conversion code | 20-a, applied | yes for memory (3.5x without the anchors); kept |
| [21](../../../reussir-bugs/21-unterminated-placeholder.md) | bug | `[` escaped in the string literal table | 21-a, applied | no; kept (policy, and free) |
| [22](../../../reussir-bugs/22-wildcard-wide-enum.md) | cost | `l2r_sink` in wildcard arms | 22-a, applied | no; kept (policy) |
| [23](../../../reussir-bugs/23-polyffi-link.md) | cost | none | 23-a, applied | n/a |
| [24](../../../reussir-bugs/24-matexp-state-order.md) | bug | none (no difference seen in lean2rr output) | 24-a, applied | n/a |
| [25](../../../reussir-bugs/25-value-record-dag.md) | cost | none (lean2rr's `[value]` records are shallow) | none (cost) | n/a |
| [26](../../../reussir-bugs/26-launder-assume.md) | bug | none possible | fixed upstream (#651, in the base; 26-a dropped) | n/a |
| [27](../../../reussir-bugs/27-nullable-member-drop.md) | missing feature | `Nullable` not used | 27-a, applied | n/a |
| [28](../../../reussir-bugs/28-unique-carrying-join.md) | bug | none possible | 28-a, applied | n/a |
| [29](../../../reussir-bugs/29-ffi-member-mlir.md) | bug | none (affects MLIR dumps only) | 29-a, applied | n/a |
| [30](../../../reussir-bugs/30-call-lowering-lookup.md) | cost | none | 30-a, applied | n/a |
| [31](../../../reussir-bugs/31-deep-expression-stack.md) | bug | `Outline` bounds nesting | 31-a, applied | n/a |
| [32](../../../reussir-bugs/32-emit-mlir-size.md) | cost | none (affects `--emit mlir` only) | none (cost) | n/a |
| [33](../../../reussir-bugs/33-rc-trailing-text.md) | bug | none (hand-written MLIR only) | 33-a, applied | n/a |
| [34](../../../reussir-bugs/34-executable-textrel.md) | bug | `scripts/l2r.py` passes `--relocation-mode pic` (as native Lean, a PIE without text relocations) | 34-a, applied | keep: harmless with 34-a, and needed without it |
| [35](../../../reussir-bugs/35-texture-rustc-runs.md) | cost | none; `scripts/l2r.py` sets `REUSSIR_FFI_CACHE_DIR` (`runtime/leanrt/target/polyffi-cache`) for the patch's cache, and the `rustc-native` script names lean-runtime's build | 35-a, applied | n/a: uses the patch, ignored without it |
| [36](../../../reussir-bugs/36-trampoline-inline.md) | missed optimization | read textures kept small (the view protocol, [ownership.md](../ownership.md#reads-give-their-reference-up-first-for-a-view)); three reads (a box; a `Nat` or `Int` element at its type) stay calls at a cold call site, which `tests/runtime/ffi-inline-check.sh` allows in `RtReadsDeep` only | none (36-a and 36-b parked: the gain is too small) | n/a |
| [38](../../../reussir-bugs/38-tagged-top-bits.md) | missing feature | none: the one-word `Box` keeps its payload's type number in the top 16 bits | 38-a, applied | n/a: `scripts/l2r.py` requires it |
| [39](../../../reussir-bugs/39-alias-release-donor.md) | missed optimization | avoided: a field put back into a rebuilt node is boxed again from its unboxed value ([records.md](../representations/records.md#a-field-is-read-at-its-binders-type-once)); passing the field's own box (commit 3f0cb30, reverted) left a dead release of the unboxed value that token reuse preferred to the matched cell (`RtProbeBump`) | none (missed optimization) | n/a |
| [40](../../../reussir-bugs/40-drain-end-hook.md) | missing feature | none since switch step 6 ([correctness-bugs.md](correctness-bugs.md#the-drain-end-hook-local-patch-40-a)) | 40-a, applied | n/a: `scripts/l2r.py` requires it |
| [41](../../../reussir-bugs/41-tagged-ffi-objects.md) | missing feature | none: `Nat` and `Int` are tagged handles ([nat-int.md](../representations/nat-int.md)) | 41-a, applied | n/a: the prelude declares `Nat` and `Int` `tagged` |
| [46](../../../reussir-bugs/46-mimalloc-arena-purge.md) | issue (dependency: mimalloc v2.2.4) | leanrt sets mimalloc's `arena_purge_mult` to 0 on v2.1.8 to v2.2.7, so free arena memory goes back to the OS at once ([startup/entry.md](../startup/entry.md#free-arena-memory-goes-back-to-the-os-at-once-mimalloc-v218-to-v227)) | none (a newer `libmimalloc-sys`, 0.1.49 or later, parked) | n/a: with a fixed mimalloc the workaround turns itself off; delete it then |
