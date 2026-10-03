# Reussir build-time costs and bugs

These do not change what a program computes, only how long rrc takes and
how much memory it uses. Bug files are in
[`reussir-bugs/`](../../../reussir-bugs/README.md); plan
[§10](../../translation-plan.md#10-known-divergences-and-unsupported-features)
("Build time") has the measurements. Paths: `lean2rr/LeanToReussir/` for
lean2rr's files.

### Bug 10: closure devirtualization prints types exponentially

- **What:** The driver passes `--no-closure-wpd` to rrc.
- **Why:** With `-O aggressive`, rrc prints each closure's result type,
  every named type expanded, at every vtable and indirect call site;
  lean2rr's function and `Box` types nest deeply under polymorphic
  recursion (out of memory at 16 GB on monad-transformer towers; adv3
  CN3-05, bfa3063). No classic benchmark changes by more than 1%: lean2rr
  dispatches function values itself
  ([10-closure-type-print.md](../../../reussir-bugs/10-closure-type-print.md)).
- **Where:** `scripts/l2r.py`: `main`.
- **Remove only if:** the bug is fixed (no patch yet).

### Bug 11: interprocedural SCCP is superlinear

- **What:** No workaround of its own; the other build-time workarounds
  shrink what SCCP sees. One shared representation for all uniform
  function types was tried and was worse (a hub for SCCP).
- **Why:** A cost of a stock MLIR pass
  ([11-sccp-call-graph.md](../../../reussir-bugs/11-sccp-call-graph.md)).
- **Where:** n/a.
- **Remove only if:** n/a.

### Bugs 16 and 17: nesting depth and straight-line length

- **What:** `Outline` cuts deep and long tail paths and `let` values into
  functions (recursive functions keep their loops through step values);
  long `Array Nat` literals become tables.
- **Why:** Reuse across calls is superlinear in match nesting
  ([16-nested-io-matches.md](../../../reussir-bugs/16-nested-io-matches.md),
  a cost of the opt-in flag), and rrc's memory is quadratic in a
  straight-line `Nat` function
  ([17-long-nat-block.md](../../../reussir-bugs/17-long-nat-block.md),
  cause unclear).
- **Where:** [../control-flow/outline.md](../control-flow/outline.md);
  [../startup/constants.md](../startup/constants.md#long-array-nat-literals-become-tables);
  `L2R_NO_OUTLINE` turns `Outline` off for the repros.
- **Remove only if:** both costs are gone (and the `.rr` text no longer
  grows with nesting).

### Bug 18: the `rrc` target alone does not link

- **What:** Build Reussir's default target.
- **Why:** [18-rrc-target-deps.md](../../../reussir-bugs/18-rrc-target-deps.md).
- **Where:** n/a.
- **Remove only if:** n/a.

### Bug 20: the inliner multiplies conversion code

- **What:** lean2rr marks `#[transform_anchor]` the functions that
  convert between representations (`l2r_fconv_S_T`), unbox (`l2r_unbox_…`
  to a nominal type, an array or a function type), and apply or identify
  function values of a type with wrapped variants, and the application
  functions of the function types of uniform code (types that mention
  `Box`). Reussir keeps a transform anchor out of its MLIR inliner (there
  are no transform scripts); LLVM still inlines it afterwards. `l2r_sink`
  is anchored for the same reason.
- **Why:** These functions call each other through wrapper variants and
  `Box` payloads, and polymorphic recursion through monad transformers
  makes hundreds of representations: an 8-line `StateT` tower used at `IO`
  did not build within 30 minutes or 15 GB (adv4 ST4-08; ae5104d, 01881fc);
  now 21 s and 0.4 GB. lean2rr relies on a side effect: a plain no-inline
  attribute would be the clean way
  ([20-statet-tower.md](../../../reussir-bugs/20-statet-tower.md)).
- **Where:** `Lower/Finish.lean`: `anchoredFns`; `Emit/Program.lean`:
  `LoweredProgram.render`; `lean2rr/Main.lean`: `pipeline`
  (`L2R_NO_INLINE_ANCHORS` empties the set, for the repro); required part
  `inline-anchors` in `Opt/Registry.lean`.
- **Remove only if:** Reussir's inliner stops multiplying such code, or a
  no-inline attribute replaces the anchor.

### Bug 22: a wildcard arm over a wide enum costs N^3 code

- **What:** A wildcard arm covering two or more constructors releases the
  values of wide enums (8 or more constructors) that it holds and does not
  use through one out-of-line call, `let us = l2r_sink<T>(v);` (the value
  is released at the arm's entry as before). Likewise the `unreachable`
  arm of an unboxing function releases its `Box` out of line.
- **Why:** rrc copies a wildcard arm into every constructor it covers and
  expands each release there in line, as a match over the variants: a
  derived `BEq`/`DecidableEq`/`Ord` on N constructors became N^3 code (40
  constructors: a 9-minute build, then 27 s; round 6 PRG6-02, 5324154). A
  cost, not a bug
  ([22-wildcard-wide-enum.md](../../../reussir-bugs/22-wildcard-wide-enum.md)).
- **Where:** `Lower/Code.lean`: `sinkWildcardHeld`, `hasWideRelease`,
  `wideReleaseCtors` (8); `runtime/prelude.rr`: `l2r_sink`;
  `Lower/Finish.lean`: `boxSink`; required part `wildcard-sinks` in
  `Opt/Registry.lean`.
- **Remove only if:** rrc gives a wildcard one region, or outlines wide
  releases.

### Bug 23: linking the polymorphic-FFI modules is quadratic

- **What:** No workaround. Patch 0017 (not applied) links all texture
  modules through one linker. Fewer generic instances would shrink both
  the compile and the link; the conversion-origin calls are two thirds of
  them (they go with the origin table, branch `mem-identity`).
- **Why:** A `Std.Http` program (8241 instances) spent 65 minutes linking
  ([23-polyffi-link.md](../../../reussir-bugs/23-polyffi-link.md)).
- **Where:** n/a.
- **Remove only if:** n/a.
