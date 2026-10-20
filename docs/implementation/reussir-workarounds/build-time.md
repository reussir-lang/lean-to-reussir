# Reussir build-time costs and bugs

These do not change what a program computes, only how long rrc takes and
how much memory it uses. Of the entries here, old 18 was a bug (Reussir's
own build was broken); old 10, 16, 17, 20, 22 and 35 were costs, not
bugs: rrc's output is correct, though a superlinear cost can make large
builds infeasible. Upstream Reussir `7954a367` fixes all of them (and the
costs 11 and 23, which had no workaround), so their files in
`reussir-bugs/` are gone; the headings give the old entry numbers.
lean2rr's builds use that base (`./reussir` branch `l2r-base3`,
`4c490260`); the workarounds stay until each is removed (the removed
ones are [at the end](#removed-workarounds)).
The open issue files are in
[`reussir-bugs/`](../../../reussir-bugs/README.md); plan
[§10](../../translation-plan.md#10-known-divergences-and-unsupported-features)
("Build time") has the measurements. Paths: `lean2rr/LeanToReussir/` for
lean2rr's files.

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
  are no transform scripts); LLVM still inlines it afterwards where its
  own threshold allows. (The same set, `anchoredFns`, also holds the
  once-cell computations `<name>_init` and the literal cache's slow path:
  those are out of line for code size, not for this issue; see
  `cafAccessor` and `strLitCached`. The ends of unboxings at a program
  payload type are not anchored, `boxUnboxWith`.)
- **Why:** These functions call each other through wrapper variants and
  `Box` payloads, and polymorphic recursion through monad transformers
  makes hundreds of representations: an 8-line `StateT` tower used at `IO`
  did not build within 30 minutes or 15 GB (adv4 ST4-08; ae5104d, 01881fc);
  now 21 s and 0.4 GB. lean2rr relies on a side effect: a plain no-inline
  attribute would be the clean way (a cost, not a bug: rrc's output is
  correct). Reussir #674 (commit `892be34c`, formerly a local patch) stops
  the inliner's chains of copied calls through recursive functions, so
  nothing explodes without the anchors any more, but the inliner's
  ordinary inlining of this code still costs: measured again on Reussir
  `7954a367` (rrc alone, with the anchors / without the conversion
  anchors), the old repro `reussir-bugs/repros/bug20-statet-tower.lean`
  (in git history before 92bec72b) 3.1 / 7.0 s and
  153 / 295 MB; adv4 St4PolyP1a (the tower used at `IO`) 3.0 / 7.9 s and
  154 / 305 MB; adv3 Cn3PolyM1 (five towers) 11 / 35 s and 0.49 / 1.23 GB,
  `.text` +67%; Cn3PolyScalar (four towers) 18 / 70 s and 0.69 / 1.99 GB,
  `.text` 2x. On the benchmark's large programs the anchors change little
  (Z06g 79 / 82 s, 1.91 / 1.92 GB, `.text` +0.6% without; Z01c and Z03d
  the same time and memory), and instruction counts move both ways
  (cachegrind: E10 at 100000 -4.4% without, Z03d on 30 KB +0.9%). So
  lean2rr keeps them.
  E10's gain comes from one application function of a function type with
  wrapped variants only (no `Box`), which the MLIR inliner then inlines
  into the loop; without the anchors of such functions only (the others
  kept), E10 has -4.3% instructions, and the towers take up to 26% more
  rrc time and up to 24% more memory. Of the 53 benchmark programs only E10 has such a
  function, so that variant is parked.
- **Where:** `Lower/Finish.lean`: `anchoredFns`; `Emit/Program.lean`:
  `LoweredProgram.render`; `lean2rr/Main.lean`: `pipeline`
  (`L2R_NO_INLINE_ANCHORS` empties the set, the size anchors too, for
  the repro); required part
  `inline-anchors` in `Opt/Registry.lean`.
- **Remove only if:** a no-inline attribute replaces the anchor, or the
  inliner's ordinary one-level inlining of this code stops costing build
  time and memory (on Reussir `7954a367`: 2.2 to 4 times the rrc time and
  2 to 2.9 times the memory on the tower repros without the anchors).

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

## Removed workarounds

Workarounds removed after the move to Reussir `7954a367`, with the
measurements that showed they were no longer needed.

### Old issue 10 (cost): closure devirtualization printed types exponentially

The driver passed `--no-closure-wpd` to rrc: with `-O aggressive`, rrc
printed each closure's result type, every named type expanded, at every
vtable and indirect call site, and lean2rr's function and `Box` types nest
deeply under polymorphic recursion (out of memory at 16 GB on
monad-transformer towers; adv3 CN3-05, bfa3063). Reussir #668 (commit
`b314cc81`, formerly a local patch) bounds the expansion. A cost, not a
bug: rrc's output was correct. Now `scripts/l2r.py` passes no such flag,
and the closure devirtualization of `-O aggressive` runs.

Measured on Reussir `7954a367`, rrc alone on the same `.rr`: the old
repro `reussir-bugs/repros/bug10-closure-type-print.py` (in git history
before 92bec72b) builds in 0.4 s at K = 22 and K = 26 with and without
the flag; the executables of the benchmark's Z06g, Z01c, Z03d, L06, L14,
L15, E10 and Z02 are byte-identical with and without it, and rrc's time
and peak memory are the same within noise (Z06g: 77-80 s and 1.8 GB
either way). lean2rr dispatches function values itself: a Reussir closure
exists only for a task, a thunk, an extern call and a few conversions
(`rawFnValue`), and of the 53 benchmark programs only L06 and Z02 have
one.

### Old issue 22 (cost): a wildcard arm over a wide enum cost N^3 code

A wildcard arm covering two or more constructors released the values of
wide enums (8 or more constructors) that it held and did not use through
one out-of-line call, `let us = l2r_sink<T>(v);` (`Lower/Code.lean`:
`sinkWildcardHeld`; the required part `wildcard-sinks`), and so did the
wildcard that `genApply` adds when `conv-liveness` leaves variants out,
for its arguments. rrc copies a wildcard arm into every constructor it
covers and expanded each release there in line, as a match over the
variants: a derived `BEq`/`DecidableEq`/`Ord` on N constructors became
N^3 code (40 constructors: a 9-minute build, then 27 s; round 6 PRG6-02,
5324154). A cost, not a bug. Reussir #673 (commit `80fd9a99`, formerly a
local patch) merges equal dispatch arms into one region before it expands
the releases. Now the arms release those values in line, as any other arm.

Measured on Reussir `7954a367` (rrc alone; old: with the sinks, new:
without): the old repro `reussir-bugs/repros/bug22-wildcard-wide-enum.py`
(in git history before 92bec72b) at N = 40 builds in 4.1 s and 0.30 GB
in its `wild` form and in 3.1 s and 0.24 GB in its `sink` form; adv6
P42BigEnum (18 sinks before) 11.6 s, 377 MB and 1382012 bytes of `.text`
old, 12.2 s, 392 MB and 1390076 bytes new; Z06g (55 sinks) 77 s,
1.84 GB, 5085468 bytes old, 79 s, 1.90 GB, 5120668 bytes new (+0.7%);
L15, E10, Z03d (3 to 4 sinks each) within 4 KB and noise. Instruction
counts (cachegrind, SVE-free builds): Z06g 76.1223 G either way
(-0.0003%), L15 at 1000 +0.08%, E10 at 100000 -0.01%. The sinks of E10
and Z03d were in unreachable arms; those of L15 in reachable ones.
