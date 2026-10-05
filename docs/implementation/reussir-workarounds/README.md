# Workarounds for Reussir

Everything lean2rr does because of a Reussir issue: a bug, a cost or a
limitation. The issues themselves (repro, cause, patch) are documented
one file each in [`reussir-bugs/`](../../../reussir-bugs/README.md), whose
column *Kind* says what each is: only a *bug* is erroneous behaviour;
costs, the missed optimizations (7, 36) and the missing features (13, 27) have
correct output, and their patches are optimizations or features, not
fixes ([kinds](../../../reussir-bugs/README.md#kinds)). This directory says
what lean2rr does about them and whether the patched Reussir still needs
it. Policy
([`reussir-bugs/README.md`](../../../reussir-bugs/README.md#policy)):
lean2rr's workarounds stay even when a local patch fixes the bug or
improves the cost, so that lean2rr also works with an unpatched Reussir;
the exceptions are issue 13 (a missing feature), whose patch 0014 the
runtime needs to build, and the local additions 0040 and 0050, which
lean2rr requires too (below).

- [correctness-bugs.md](correctness-bugs.md): bugs that affect the
  program rather than its build time: wrong values, rrc crashes or
  rejected programs, use after free (1, 2, 4, 5, 6, 8, 9/14, 12, 15, 19,
  21), and the drain-end hook (patch 0040). Entries 24 to 33 need nothing
  from lean2rr; for 34, `scripts/l2r.py` passes `--relocation-mode pic`
  (patch 0065 makes it rrc's default for linked products; table below).
- [build-time.md](build-time.md): a build-time bug (18) and build-time
  costs (10, 11, 16, 17, 20, 22, 23, 35).
- [limitations.md](limitations.md): Reussir behaviour that is not a bug
  but shapes lean2rr's output: intended behaviour (3), a missed
  optimization (7), a missing feature (13), the FFI boundary, `unit`, tail
  calls, `str` arguments, syntax, the driver's flags.

## Summary

`l2r-local` is the branch of `./reussir` with the applied local patches:
all 37 of them (head `d79f8b70`, since 2026-10-04; the apply list is in
[`reussir-bugs/README.md`](../../../reussir-bugs/README.md#applying-the-patches)),
including 0040 (the drain-end hook) and 0050 (tagged opaque handles, for
branch `mem-nat`), which belong to no entry
([`reussir-bugs/local-additions.md`](../../../reussir-bugs/local-additions.md)).

Column "Needed with the patch?": whether lean2rr's workaround is still
needed once the patch is applied. By the policy above, workarounds stay
either way.

| Issue | Kind | lean2rr workaround | Local patch | Needed with the patch? |
|---|---|---|---|---|
| [1](../../../reussir-bugs/01-value-enum-payload.md) | bug | only field-less `[value]` enums (`Nat`/`Int` are tagged handles, 0050) | 0020, applied | no; kept (policy) |
| [2](../../../reussir-bugs/02-reuse-field-store.md) | bug | `--no-pack-record-members`; fields ordered by alignment | 0002 (structures) and 0019 (variants), applied | no; kept (policy) |
| [3](../../../reussir-bugs/03-global-alloc-align.md) | intended | runtime allocates with `mi_malloc` | none (intended) | needed (intended behaviour) |
| [4](../../../reussir-bugs/04-recursive-type-compare.md) | bug | driver retries rrc without `--reuse-across-call` | 0004, applied | no; kept as a fallback for unknown crashes |
| [5](../../../reussir-bugs/05-one-armed-if.md) | bug | runtime diagnostics through a C trampoline | 0005, applied | no; kept (policy) |
| [6](../../../reussir-bugs/06-static-count-wrap.md) | bug | none (flag alternative not used) | 0006, applied | n/a |
| [7](../../../reussir-bugs/07-phantom-reuse-donor.md) | missed optimization | `lazy-fields`, `nullary-scrutinee`, `sink-proj` | 0007, applied | yes (0007 misses call-before-branch) |
| [8](../../../reussir-bugs/08-padding-lift.md) | bug | shape never emitted | 0018, applied | n/a |
| [9](../../../reussir-bugs/09-duplicate-bound-member.md), [14](../../../reussir-bugs/14-member-consumed-before-release.md) | bugs | none possible | 0009, applied | n/a |
| [10](../../../reussir-bugs/10-closure-type-print.md) | cost | `--no-closure-wpd` | 0024, applied | no; kept (policy) |
| [11](../../../reussir-bugs/11-sccp-call-graph.md) | cost (11b too) | none | 0032 (and 0033 for 11b), applied | n/a |
| [12](../../../reussir-bugs/12-node-cache-collision.md) | bug | none possible | 0012, applied | n/a |
| [13](../../../reussir-bugs/13-long-list-drop.md) | missing feature | runtime frees through 0014's stack | 0013-0015, applied | yes (the runtime needs 0014) |
| [15](../../../reussir-bugs/15-nullable-match-yield.md) | bug | `Nullable` not used | 0022, applied | n/a |
| [16](../../../reussir-bugs/16-nested-io-matches.md), [17](../../../reussir-bugs/17-long-nat-block.md) | costs | `Outline`; `Array Nat` literal tables | 0035 and 0031, applied | no; kept (policy, and it bounds the `.rr` text) |
| [18](../../../reussir-bugs/18-rrc-target-deps.md) | bug (build system) | build Reussir's default target | 0025, applied | no |
| [19](../../../reussir-bugs/19-cell-of-value-record.md) | bug | `ElemBox` for `[value]` records in references (`Nat`/`Int` are tagged handles, 0050) | 0023, applied | no; kept (policy) |
| [20](../../../reussir-bugs/20-statet-tower.md) | cost | `#[transform_anchor]` on conversion code | 0034, applied | yes for memory (3.5x without the anchors); kept |
| [21](../../../reussir-bugs/21-unterminated-placeholder.md) | bug | `[` escaped in the string literal table | 0016, applied | no; kept (policy, and free) |
| [22](../../../reussir-bugs/22-wildcard-wide-enum.md) | cost | `l2r_sink` in wildcard arms | 0030, applied | no; kept (policy) |
| [23](../../../reussir-bugs/23-polyffi-link.md) | cost | none | 0017, applied | n/a |
| [24](../../../reussir-bugs/24-matexp-state-order.md) | bug | none (no difference seen in lean2rr output) | 0026, applied | n/a |
| [25](../../../reussir-bugs/25-value-record-dag.md) | cost | none (lean2rr's `[value]` records are shallow) | none (cost) | n/a |
| [26](../../../reussir-bugs/26-launder-assume.md) | bug | none possible | 0021, applied | n/a |
| [27](../../../reussir-bugs/27-nullable-member-drop.md) | missing feature | `Nullable` not used | 0027, applied | n/a |
| [28](../../../reussir-bugs/28-unique-carrying-join.md) | bug | none possible | 0060, applied | n/a |
| [29](../../../reussir-bugs/29-ffi-member-mlir.md) | bug | none (affects MLIR dumps only) | 0061, applied | n/a |
| [30](../../../reussir-bugs/30-call-lowering-lookup.md) | cost | none | 0062, applied | n/a |
| [31](../../../reussir-bugs/31-deep-expression-stack.md) | bug | `Outline` bounds nesting | 0063, applied | n/a |
| [32](../../../reussir-bugs/32-emit-mlir-size.md) | cost | none (affects `--emit mlir` only) | none (cost) | n/a |
| [33](../../../reussir-bugs/33-rc-trailing-text.md) | bug | none (hand-written MLIR only) | 0064, applied | n/a |
| [34](../../../reussir-bugs/34-executable-textrel.md) | bug | `scripts/l2r.py` passes `--relocation-mode pic` (as native Lean, a PIE without text relocations) | 0065, applied | keep: harmless with 0065, and needed without it |
| [35](../../../reussir-bugs/35-texture-rustc-runs.md) | cost | none; `scripts/l2r.py` sets `REUSSIR_FFI_CACHE_DIR` (`runtime/leanrt/target/polyffi-cache`) for the patch's cache, and the `rustc-native` script names lean-runtime's build | 0066, applied | n/a: uses the patch, ignored without it |
| [36](../../../reussir-bugs/36-trampoline-inline.md) | missed optimization | read textures kept small (the view protocol, [ownership.md](../ownership.md#reads-give-their-reference-up-first-for-a-view)) | none (missed optimization) | needed (every texture LLVM judges too costly at a cold call site stays a call) |
