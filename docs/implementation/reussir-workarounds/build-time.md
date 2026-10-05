# Reussir build-time costs and bugs

These do not change what a program computes, only how long rrc takes and
how much memory it uses. Of the entries here, 18 is a bug (Reussir's own
build is broken); 10, 11, 16, 17, 20, 22, 23 and 35 are costs, not bugs:
rrc's output is correct, though a superlinear cost can make large builds
infeasible, and their patches are optimizations. The issue files are in
[`reussir-bugs/`](../../../reussir-bugs/README.md); plan
[§10](../../translation-plan.md#10-known-divergences-and-unsupported-features)
("Build time") has the measurements. Paths: `lean2rr/LeanToReussir/` for
lean2rr's files.

### Issue 10 (cost): closure devirtualization prints types exponentially

- **What:** The driver passes `--no-closure-wpd` to rrc.
- **Why:** With `-O aggressive`, rrc prints each closure's result type,
  every named type expanded, at every vtable and indirect call site;
  lean2rr's function and `Box` types nest deeply under polymorphic
  recursion (out of memory at 16 GB on monad-transformer towers; adv3
  CN3-05, bfa3063). No classic benchmark changes by more than 1%: lean2rr
  dispatches function values itself
  ([10-closure-type-print.md](../../../reussir-bugs/10-closure-type-print.md);
  a cost, not a bug: rrc's output is correct; patch 0024, an optimization,
  applied).
- **Where:** `scripts/l2r.py`: `main`.
- **Remove only if:** not needed with 0024 (applied), but kept: by the
  policy lean2rr also works with an unpatched Reussir, and devirtualization
  buys lean2rr nothing measurable.

### Issue 11 (cost): interprocedural SCCP is superlinear

- **What:** No workaround of its own; the other build-time workarounds
  shrink what SCCP sees. One shared representation for all uniform
  function types was tried and was worse (a hub for SCCP).
- **Why:** A cost of a stock MLIR pass, not a bug
  ([11-sccp-call-graph.md](../../../reussir-bugs/11-sccp-call-graph.md));
  patch 0032 (an optimization, applied) runs it across calls only within
  a budget of call sites, and 0033 (an optimization, applied) removes 11b,
  a quadratic glue lookup in Reussir's own code (also a cost).
- **Where:** n/a.
- **Remove only if:** n/a.

### Issues 16 and 17 (costs): nesting depth and straight-line length

- **What:** `Outline` cuts deep and long tail paths and `let` values into
  functions (recursive functions keep their loops through step values);
  long `Array Nat` literals become tables.
- **Why:** Reuse across calls is superlinear in match nesting
  ([16-nested-io-matches.md](../../../reussir-bugs/16-nested-io-matches.md),
  a cost of the opt-in flag; patch 0035, an optimization, applied), and
  rrc's memory was quadratic in a straight-line `Nat` function
  ([17-long-nat-block.md](../../../reussir-bugs/17-long-nat-block.md):
  a cost of `convert-scf-to-cf` with pattern rollback; patch 0031, an
  optimization, applied). Neither is a bug: rrc's output is correct.
- **Where:** [../control-flow/outline.md](../control-flow/outline.md);
  [../startup/constants.md](../startup/constants.md#long-array-nat-literals-become-tables);
  `L2R_NO_OUTLINE` turns `Outline` off for the repros.
- **Remove only if:** both costs are gone with 0031 and 0035 (applied),
  and the `.rr` text no longer grows with nesting; kept meanwhile (policy,
  and it still bounds the `.rr` text).

### Bug 18: the `rrc` target alone does not link

- **What:** Build Reussir's default target.
- **Why:** [18-rrc-target-deps.md](../../../reussir-bugs/18-rrc-target-deps.md)
  (patch 0025, applied: the `rrc` target alone now links).
- **Where:** n/a.
- **Remove only if:** n/a.

### Issue 20 (cost): the inliner multiplies conversion code

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
  ([20-statet-tower.md](../../../reussir-bugs/20-statet-tower.md); a cost,
  not a bug: rrc's output is correct). Patch 0034 (an optimization,
  applied) stops the inliner's chains of copied calls through
  recursive functions: without the anchors the repro now takes 0.77 GB
  instead of 2.9 GB, against 0.22 GB with them, so lean2rr keeps them.
- **Where:** `Lower/Finish.lean`: `anchoredFns`; `Emit/Program.lean`:
  `LoweredProgram.render`; `lean2rr/Main.lean`: `pipeline`
  (`L2R_NO_INLINE_ANCHORS` empties the set, for the repro); required part
  `inline-anchors` in `Opt/Registry.lean`.
- **Remove only if:** a no-inline attribute replaces the anchor, or the
  inliner's ordinary one-level inlining of this code stops costing
  memory (with 0034 it is still 3.5x).

### Issue 22 (cost): a wildcard arm over a wide enum costs N^3 code

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
  ([22-wildcard-wide-enum.md](../../../reussir-bugs/22-wildcard-wide-enum.md));
  patch 0030 (an optimization, applied) merges a wildcard arm's copies
  into one region.
- **Where:** `Lower/Code.lean`: `sinkWildcardHeld`, `hasWideRelease`,
  `wideReleaseCtors` (8); `runtime/prelude.rr`: `l2r_sink`;
  `Lower/Finish.lean`: `boxSink`, and the wildcard `genApply` adds when
  `conv-liveness` leaves variants out (its arguments sunk:
  [../conversions/liveness.md](../conversions/liveness.md#an-application-function-with-variants-left-out-ends-in-a-wildcard));
  required part `wildcard-sinks` in `Opt/Registry.lean`.
- **Remove only if:** not needed with 0030 (applied: rrc now gives a
  wildcard one region), but kept: by the policy lean2rr also works with an
  unpatched Reussir.

### Issue 23 (cost): linking the polymorphic-FFI modules is quadratic

- **What:** No workaround. Patch 0017 (an optimization, applied) links all
  texture modules through one linker. Fewer generic instances would shrink
  both the compile and the link (at the time two thirds of them were the
  conversion-origin calls, which went with the origin table: mem-identity,
  7869383).
- **Why:** A `Std.Http` program (8241 instances) spent 65 minutes linking
  ([23-polyffi-link.md](../../../reussir-bugs/23-polyffi-link.md); a cost,
  not a bug: rrc's output is correct).
- **Where:** n/a.
- **Remove only if:** n/a.

### Issue 35 (cost): every texture is compiled again on every build

- **What:** `scripts/l2r.py` sets `REUSSIR_FFI_CACHE_DIR` for rrc to
  `runtime/leanrt/target/polyffi-cache` unless the caller sets it (empty:
  off), so that rrc with patch 0066 (an optimization, applied since
  2026-10-04) takes the bitcode of
  textures it compiled before from there. The `rustc-native` script's
  text names lean-runtime's build (`# lean-runtime build <digest>`):
  rrc's key hashes the script and the `--polyffi-libdir` directories, and
  cargo's build of lean-runtime (once it has dependencies) puts its rlibs
  in none of them. Nothing removes old entries (about 8 KB each, a new set
  of about 470 per change of leanrt, lean-runtime, Reussir's runtime or
  the toolchain); delete the directory to reclaim the space. The key
  hashes the rlibs' bytes, so `build_locked` runs rustc for leanrt and
  lean-runtime in the crate's directory: rustc records its working
  directory in an rlib, and a rebuild from another directory would
  otherwise change every key (the recorded source paths, which panic
  messages show, stay absolute and unchanged).
- **Why:** rrc runs rustc once per texture, and lean2rr writes the whole
  prelude into every program: about 470 rustc runs, 13 s of a small
  program's 16 s of rrc; with the cache full, 3 s
  ([35-texture-rustc-runs.md](../../../reussir-bugs/35-texture-rustc-runs.md);
  a cost, not a bug: rrc's output is correct).
- **Where:** `scripts/l2r.py`: `main`, `rustc_wrapper`, `build_locked`.
- **Remove only if:** n/a (not a workaround: it turns the patch's cache
  on; an rrc without the patch ignores the variable).
