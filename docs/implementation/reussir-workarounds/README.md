# Workarounds for Reussir

Everything lean2rr does because of a Reussir bug, cost or limitation. The
bugs themselves (repro, cause, patch) are documented one file each in
[`reussir-bugs/`](../../../reussir-bugs/README.md); this directory says
what lean2rr does about them and whether the patched Reussir still needs
it. Policy
([`reussir-bugs/README.md`](../../../reussir-bugs/README.md#policy)):
lean2rr's workarounds stay even when a local patch fixes the bug, so that
lean2rr also works with an unpatched Reussir; the exception is bug 13,
whose patch 0014 the runtime needs to build.

- [correctness-bugs.md](correctness-bugs.md): entries that affect the
  program rather than its build time: wrong values, rrc crashes or
  rejected programs, use after free, a missed optimization (7) and a
  missing feature (13) (1, 2, 4, 5, 6, 7, 8, 9/14, 12, 13, 15, 19, 21), and
  the drain-end hook (patch 0040).
- [build-time.md](build-time.md): build-time costs and bugs (10, 11, 16,
  17, 18, 20, 22, 23).
- [limitations.md](limitations.md): Reussir behaviour that is not a bug
  but shapes lean2rr's output (the FFI boundary, `unit`, tail calls,
  `str` arguments, syntax, the driver's flags).

## Summary

`l2r-local` is the branch of `./reussir` with the applied local patches:
0006, 0004, 0002, 0007, 0009, 0005, 0013, 0012, 0014, 0015. Patches 0016
and 0017 are in `reussir-bugs/patches/` but not applied. Patch 0040 is not
applied either; at b299aab it is
`reussir-patches/0040-l2r-local-drop-call-the-host-s-function-when-a-drain.patch`
(report: `reussir-patches/details/0040.md`), and it moves with the other
patches when the `reussir-bugs/` reorganization is merged.

Column "Needed with the patch?": whether lean2rr's workaround is still
needed once the patch is applied. By the policy above, workarounds stay
either way.

| Bug | lean2rr workaround | Local patch | Needed with the patch? |
|---|---|---|---|
| [1](../../../reussir-bugs/01-value-enum-payload.md) | only field-less `[value]` enums (and `Nat`/`Int`) | none yet | no patch; needed |
| [2](../../../reussir-bugs/02-reuse-field-store.md) | `--no-pack-record-members`; fields ordered by alignment | 0002 (structures only), applied | yes (variants unpatched) |
| [3](../../../reussir-bugs/03-global-alloc-align.md) | runtime allocates with `mi_malloc` | none (intended) | needed (intended behaviour) |
| [4](../../../reussir-bugs/04-recursive-type-compare.md) | driver retries rrc without `--reuse-across-call` | 0004, applied | no; kept as a fallback for unknown crashes |
| [5](../../../reussir-bugs/05-one-armed-if.md) | runtime diagnostics through a C trampoline | 0005, applied | no; kept (policy) |
| [6](../../../reussir-bugs/06-static-count-wrap.md) | none (flag alternative not used) | 0006, applied | n/a |
| [7](../../../reussir-bugs/07-phantom-reuse-donor.md) | `lazy-fields`, `nullary-scrutinee`, `sink-proj` | 0007, applied | yes (0007 misses call-before-branch) |
| [8](../../../reussir-bugs/08-padding-lift.md) | shape never emitted | none yet | n/a |
| [9](../../../reussir-bugs/09-duplicate-bound-member.md), [14](../../../reussir-bugs/14-member-consumed-before-release.md) | none possible | 0009, applied | n/a |
| [10](../../../reussir-bugs/10-closure-type-print.md) | `--no-closure-wpd` | none yet | no patch; needed |
| [11](../../../reussir-bugs/11-sccp-call-graph.md) | none | none (cost) | n/a |
| [12](../../../reussir-bugs/12-node-cache-collision.md) | none possible | 0012, applied | n/a |
| [13](../../../reussir-bugs/13-long-list-drop.md) | runtime frees through 0014's stack | 0013-0015, applied | yes (the runtime needs 0014) |
| [15](../../../reussir-bugs/15-nullable-match-yield.md) | `Nullable` not used | none yet | n/a |
| [16](../../../reussir-bugs/16-nested-io-matches.md), [17](../../../reussir-bugs/17-long-nat-block.md) | `Outline`; `Array Nat` literal tables | none (cost / unclear) | no patch; needed |
| [18](../../../reussir-bugs/18-rrc-target-deps.md) | build Reussir's default target | none yet | n/a |
| [19](../../../reussir-bugs/19-cell-of-value-record.md) | `L2RNatRef`/`L2RIntRef`; `ElemBox` in references | none yet | no patch; needed |
| [20](../../../reussir-bugs/20-statet-tower.md) | `#[transform_anchor]` on conversion code | none (unclear) | no patch; needed |
| [21](../../../reussir-bugs/21-unterminated-placeholder.md) | `[` escaped in the string literal table | 0016, not applied | no; kept (policy, and free) |
| [22](../../../reussir-bugs/22-wildcard-wide-enum.md) | `l2r_sink` in wildcard arms | none (cost) | no patch; needed |
| [23](../../../reussir-bugs/23-polyffi-link.md) | none | 0017, not applied | n/a |
