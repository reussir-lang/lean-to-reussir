# Reussir build-time costs and bugs

These do not change what a program computes, only how long rrc takes and
how much memory it uses. Of the entries here, old 18 was a bug (Reussir's
own build was broken); old 10, 16, 17, 20, 22 and 35 were costs, not
bugs: rrc's output is correct, though a superlinear cost can make large
builds infeasible. Upstream Reussir `7954a367` fixes all of them (and the
costs 11 and 23, which had no workaround), so their files in
`reussir-bugs/` are gone; the headings give the old entry numbers.
lean2rr's builds use that base (`./reussir` branch `l2r-base3`,
`4c490260`); the workarounds stay until each is removed.
The open issue files are in
[`reussir-bugs/`](../../../reussir-bugs/README.md); plan
[§10](../../translation-plan.md#10-known-divergences-and-unsupported-features)
("Build time") has the measurements. Paths: `lean2rr/LeanToReussir/` for
lean2rr's files.

### Old issue 10 (cost): closure devirtualization printed types exponentially

- **What:** The driver passes `--no-closure-wpd` to rrc.
- **Why:** With `-O aggressive`, rrc prints each closure's result type,
  every named type expanded, at every vtable and indirect call site;
  lean2rr's function and `Box` types nest deeply under polymorphic
  recursion (out of memory at 16 GB on monad-transformer towers; adv3
  CN3-05, bfa3063). No classic benchmark changes by more than 1%: lean2rr
  dispatches function values itself (a cost, not a bug: rrc's output is
  correct; fixed upstream in Reussir #668, commit `b314cc81`, formerly a
  local patch).
- **Where:** `scripts/l2r.py`: `main`.
- **Remove only if:** removable after the move to Reussir 7954a367;
  devirtualization buys lean2rr nothing measurable, so the flag may stay.

### Old issues 16 and 17 (costs): nesting depth and straight-line length

- **What:** `Outline` cuts deep and long tail paths and `let` values into
  functions (recursive functions keep their loops through step values).
  (Long `Array Nat` literals were tables, pushed by the runtime, while an
  `Array Nat` was a one-word `LNatArr`; an array of `Box`es has none.)
- **Why:** Reuse across calls was superlinear in match nesting (a cost
  of the opt-in flag; fixed upstream in Reussir #672, commit `4dc9e469`),
  and rrc's memory was quadratic in a straight-line `Nat` function (a
  cost of `convert-scf-to-cf` with pattern rollback; fixed upstream in
  Reussir #670, commit `211c97bb`). Both were local patches before.
  Neither is a bug: rrc's output is correct.
- **Where:** [../control-flow/outline.md](../control-flow/outline.md);
  `L2R_NO_OUTLINE` turns `Outline` off for the repros.
- **Remove only if:** removable after the move to Reussir 7954a367 as a
  workaround, once the `.rr` text no longer grows with nesting; kept
  meanwhile (it still bounds the `.rr` text).

### Old bug 18: the `rrc` target alone did not link

- **What:** Build Reussir's default target.
- **Why:** the `rrc` target did not build the archives it links (fixed
  upstream in Reussir #684, commit `2d65de01`; formerly a local patch).
- **Where:** n/a.
- **Remove only if:** removable after the move to Reussir 7954a367.

### Old issue 20 (cost): the inliner multiplies conversion code

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
  attribute would be the clean way (a cost, not a bug: rrc's output is
  correct). Reussir #674 (commit `892be34c`, formerly a local patch) stops
  the inliner's chains of copied calls through recursive functions: with
  the local patch on the old stack, the repro took 0.77 GB without the
  anchors instead of 2.9 GB, against 0.22 GB with them, so lean2rr keeps
  them.
- **Where:** `Lower/Finish.lean`: `anchoredFns`; `Emit/Program.lean`:
  `LoweredProgram.render`; `lean2rr/Main.lean`: `pipeline`
  (`L2R_NO_INLINE_ANCHORS` empties the set, for the repro); required part
  `inline-anchors` in `Opt/Registry.lean`.
- **Remove only if:** removable after the move to Reussir 7954a367 only
  if the memory is measured again then: a no-inline attribute replaces
  the anchor, or the inliner's ordinary one-level inlining of this code
  stops costing memory (with the old local patch it was still 3.5x).

### Old issue 22 (cost): a wildcard arm over a wide enum cost N^3 code

- **What:** A wildcard arm covering two or more constructors releases the
  values of wide enums (8 or more constructors) that it holds and does not
  use through one out-of-line call, `let us = l2r_sink<T>(v);` (the value
  is released at the arm's entry as before). The calls come in the order
  of the values' first use in the other arms (`rrFreeVarsInOrder`), not
  by name: names carry lean2rr's one counter. Likewise the `unreachable`
  arm of an unboxing function releases its `Box` out of line.
- **Why:** rrc copies a wildcard arm into every constructor it covers and
  expands each release there in line, as a match over the variants: a
  derived `BEq`/`DecidableEq`/`Ord` on N constructors became N^3 code (40
  constructors: a 9-minute build, then 27 s; round 6 PRG6-02, 5324154). A
  cost, not a bug. Reussir #673 (commit `80fd9a99`, formerly a local
  patch) merges equal dispatch arms into one region: the 30-constructor
  repro builds in 2.6 s on Reussir `7954a367`.
- **Where:** `Lower/Code.lean`: `sinkWildcardHeld`, `hasWideRelease`,
  `wideReleaseCtors` (8); `runtime/prelude.rr`: `l2r_sink`;
  `Lower/Finish.lean`: `boxSink`, and the wildcard `genApply` adds when
  `conv-liveness` leaves variants out (its arguments sunk:
  [../conversions/liveness.md](../conversions/liveness.md#an-application-function-with-variants-left-out-ends-in-a-wildcard));
  required part `wildcard-sinks` in `Opt/Registry.lean`.
- **Remove only if:** removable after the move to Reussir 7954a367.

### Old issue 35 (cost): every texture was compiled again on every build

- **What:** `scripts/l2r.py` sets `REUSSIR_FFI_CACHE_DIR` for rrc to
  `runtime/leanrt/target/polyffi-cache` unless the caller sets it (empty:
  off), so that rrc's texture cache (a local patch since 2026-10-04;
  upstream Reussir #690, commit `84336b63`, reads the same variable) takes
  the bitcode of
  textures it compiled before from there. The `rustc-native` script's
  text names lean-runtime's build (`# lean-runtime build <digest>`):
  rrc's key hashes the script and the `--polyffi-libdir` directories, and
  cargo's build of lean-runtime (once it has dependencies) puts its rlibs
  in none of them. A change of leanrt, lean-runtime, Reussir's runtime or
  the toolchain makes a new set of entries (about 8 KB each). rrc prunes
  the directory (`llvm::pruneCache`): it removes the entries
  (`llvmcache-*`) not read for a week and keeps their total at most
  1 GiB. It does not remove other files, such as the `<hex>.bc` entries of
  the old local patch (deleted once, at the move to Reussir `7954a367`).
  A `%` in the directory's path makes #690's cache store nothing (the old
  patch's review finding FCR-03, not in #690); lean2rr's default path
  has none. The key hashes the rlibs' bytes, so `build_locked` runs rustc
  for leanrt and lean-runtime in the crate's directory: rustc records its
  working directory in an rlib, and a rebuild from another directory would
  otherwise change every key (the recorded source paths, which panic
  messages show, stay absolute and unchanged).
- **Why:** rrc runs rustc once per texture, and lean2rr wrote the whole
  prelude into every program: about 470 rustc runs, 13 s of a small
  program's 16 s of rrc; with the cache full, 3 s (a cost, not a bug:
  rrc's output is correct). Since the optimization
  `prelude-liveness`, the text has only the prelude functions the program
  uses (a one-line program: 75 textures;
  [optional-passes.md](../optional-passes.md#only-the-prelude-functions-that-a-program-uses-are-kept-prelude-liveness)),
  so an empty cache costs much less; the cache still saves the rest.
- **Where:** `scripts/l2r.py`: `main`, `rustc_wrapper`, `build_locked`.
- **Remove only if:** n/a (not a workaround: it turns the cache on; an
  rrc without a cache ignores the variable).
