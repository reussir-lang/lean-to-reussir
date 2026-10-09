# Reussir issues and local patches

This directory records every Reussir problem that lean2rr has met, and the
local patches that lean2rr's builds apply to Reussir.

- **Entries.** One file per problem, `NN-name.md`, where NN is the entry
  number. An entry gives a repro, the cause in Reussir's source where it is
  known, what lean2rr does about the problem and, if there is a patch, the
  patch explained, with its review. Each entry is a numbered *issue*; its
  [kind](#kinds) says whether it is a bug.
- **Patches.** [`patches/`](patches/) holds the patch files.
  [`patches/series`](patches/series) gives the order in which to apply
  them ([applying the patches](#applying-the-patches)).
- **Repros.** [`repros/`](repros/) holds the repro programs and `run.sh`,
  which builds and runs them ([running the repros](#running-the-repros)).

Reussir revision: `943f2195`, upstream `main` on 2026-10-07. The
checkout at `./reussir` is not part of this repository. Its branch
`l2r-base2` (head `b2e4a47e`) is 943f2195 plus the 35 patches of the series,
as they are since 2026-10-09, when the fix of
[issue 47](47-unlink-provenance.md) was folded into 13-c; `l2r-local` is
at the same head, and lean2rr's builds use it. Branch `l2r-base2-pre47` (head `71f17ae2`) keeps the stack with
13-c as it was before, the one lean2rr's builds used from 2026-10-07. Upstream merged
five of lean2rr's bug fixes (26-a, 02-a, 09-a, 04-a and 05-a, pull
requests #651 to #655), so the series dropped them when its base moved
from `ef922049` to `943f2195`. Older branches of the checkout:
`l2r-trim` (head `79c1d5f2`) is `ef922049` plus the 40 patches of the
series before that move, made on 2026-10-07, when the optimizations
07-a, 36-a and 36-b were parked ([parked patches](#parked-patches));
`l2r-local` (head `136d9a9f`) is the series as it was before: 43
patches, the parked three and the earlier form of 09-a included. (The
`l2r-local` before 2026-10-03, the first twelve patches, is kept as
branch `l2r-local-pre-final`.)

## Names

- **Entry numbers** run from 1 to 47: 46 entries, because number 37 is
  reserved (another track will use it for its patch: value records across
  the FFI boundary). The next free number is 48.
- **A patch file** is named `NN-x-slug.patch`. NN is the number of its
  entry. The letter x gives the order of the entry's patches (a, b, c,
  ...). The slug is a short description. Every patch belongs to exactly one
  entry. In the text, a patch is named by NN-x: 13-b is the second patch of
  issue 13.
- **Patch file contents** are `git format-patch` output of the commits
  of `l2r-base2`, against `943f2195`. A file's subject line is the subject
  of its commit on `l2r-local`, and these subjects use older words: "bug
  NN" or "issue NN" means entry NN, whatever its kind; "13b" and "11b" are
  parts of entries 13 and 11. The subjects of 40-a and 41-a have no
  number.
- **Old numbers.** Until 2026-10-06 the patch files had four-digit numbers
  (0002 to 0069), and commit messages and older notes cite them. The
  [table of old numbers](#old-patch-numbers) gives the new name of each.
- Older text and commit messages say "bug NN" for every entry, whatever
  its kind: read it as "issue NN". The directory keeps its name,
  `reussir-bugs/`, and the repro files theirs (`bugNN-*`), so that paths
  stay valid.

## Kinds

Only a *bug* is erroneous behaviour. Every other kind is correct
behaviour by Reussir's own rules and promises: rrc's output is right. A
patch for an issue that is not a bug is an improvement (an optimization or
a feature), not a fix.

- *bug*: reproducible, erroneous behaviour: a crash, a wrong result, valid
  code rejected, a broken build or broken build artifacts. Nothing else.
  Its patch is a fix.
- *bug (latent UB; no miscompile seen)*: a bug in Reussir's Rust code
  that breaks a rule of the language (for example pointer provenance), so
  that its behaviour is undefined: Miri shows it reproducibly, but no
  build is known to give a wrong result (47). The compiler may rely on the
  rule, so a new compiler version or other inlining can turn it into a
  wrong result. Its patch is a fix.
- *cost*: correct, but slow or big (build time, memory, run time; also
  debug output). Its patch, if any, is an optimization. A superlinear build
  cost can make large builds infeasible (time or memory) while the output
  stays correct (10, 11, 16, 17, 20, 22, 23, 30). It is still a cost,
  whether it lies in a stock pass, an opt-in flag, a design or Reussir's
  own code.
- *missed optimization*: correct output, slower than it could be. Its
  patch, if any, is an optimization.
- *missing feature*: something Reussir never promised that lean2rr needs
  (bounded-depth frees, a hook at the end of a free, handles that may be a
  number). Its patch is a feature.
- *issue (dependency)*: an error in a library that Reussir pins, not in
  Reussir's own code (46: mimalloc v2.2.4). lean2rr works around it
  outside Reussir; the change on Reussir's side is a newer version of the
  dependency.
- *intended*: documented behaviour. No entry has this kind alone since
  2026-10-06: entry 3's 16-byte alignment is intended, but the slow frees
  it caused were avoidable, so entry 3 is a cost.

## Status

One row per entry, grouped by kind. Column *Patches*: the entry's patch
files, in apply order; "none" marks an entry that stays unpatched (the
reason is in its file); "fixed upstream" names the pull request on
github.com/reussir-lang/reussir and its commit on `main` that carry a
dropped patch. Column *Review*: the adversarial review round and its
result ([Review](#review)). Column *Applied*: whether the patches are on
`./reussir`'s `l2r-base2` (every patch of the series is); "parked" marks
a patch outside the series ([parked patches](#parked-patches)), and
"upstream" an entry whose fix is in Reussir's `main` (the base
`943f2195` includes it).

| # | Kind | Effect | Affects lean2rr output? | lean2rr workaround | Patches | Review | Applied |
|---|---|---|---|---|---|---|---|
| [1](01-value-enum-payload.md) | bug | `[value]` enum payload bytes lost when a variant is moved | no, shape avoided | emits only unaffected `[value]` enums | [01-a](patches/01-a-value-enum-arm-bytes.patch) | rv8/reussir: no defect | yes |
| [2](02-reuse-field-store.md) | bug | in-place reuse skips the store of a field that sits elsewhere in the new cell | structures: yes, wrong values; variants: no | variants: `--no-pack-record-members` and fields ordered by alignment | structures: fixed upstream (#652, `3be77a64`; 02-a dropped); variants: [02-b](patches/02-b-variant-field-store.patch) | 02-a passed (rounds 1-3); 02-b rv8/reussir: no defect | 02-a upstream; 02-b yes (upstream #656 open) |
| [4](04-recursive-type-compare.md) | bug | rrc recurses forever on two equal recursive types (SIGSEGV) | yes, rrc crash | driver retries without `--reuse-across-call` | fixed upstream (#654, `634fb551`; 04-a dropped) | passed | upstream |
| [5](05-one-armed-if.md) | bug | TokenReuse crashes on a one-armed `if` (SIGSEGV) | yes, rrc crash | prelude panics avoid the shape; user code can still hit it | fixed upstream (#655, `943f2195`; 05-a dropped) | passed | upstream |
| [6](06-static-count-wrap.md) | bug, with a flag workaround | a static cell is freed after about 2^32 references | yes, crash | `--nullary-variant-encoding arch-independent` or `boxed` (not used: 06-a keeps the default encoding's speed; to be remeasured on an idle machine) | [06-a](patches/06-a-immediate-count-wrap.patch) | passed | yes |
| [8](08-padding-lift.md) | bug | padding "lift" gives LLVM a larger layout than Reussir's | no, shape never emitted | - | [08-a](patches/08-a-padding-widening.patch) | rv8/reussir: no defect | yes |
| [9](09-duplicate-bound-member.md) | bug | a member used twice loses a reference (use after free) | yes, through Reussir's inliner | none | fixed upstream (#653, `0ed0f243`, also fixes 14; 09-a dropped) | passed (revised after round 2) | upstream |
| [12](12-node-cache-collision.md) | bug (in cstree) | the parser swaps syntax subtrees whose hashes collide | yes, wrong code or bogus errors on very large files | none | [12-a](patches/12-a-no-hash-node-cache.patch) | passed | yes |
| [14](14-member-consumed-before-release.md) | bug | a member consumed before the release loses a reference (use after free) | yes, through Reussir's inliner | none | none of its own: fixed upstream with entry 9 (#653, `0ed0f243`; 09-a dropped) | passed | upstream |
| [15](15-nullable-match-yield.md) | bug | a `match` on a `Nullable` yielding a counted value does not compile | no, `Nullable` not used | - | [15-a](patches/15-a-yield-parent-check.patch) | rv7/p22: no defect | yes |
| [18](18-rrc-target-deps.md) | bug (build system) | the `rrc` build target alone does not link | no, Reussir's build only | build the default target | [18-a](patches/18-a-archive-build-order.patch) | rv7/p22: no defect | yes |
| [19](19-cell-of-value-record.md) | bug | a `Cell` of a `[value]` record with counted members does not compile | yes, compile error | `[value]` records in references boxed (`Nat`/`Int` are tagged handles since 41-a) | [19-a](patches/19-a-cell-value-record-glue.patch) (with 11-b's composition fix) | rv7/p22 rounds 1-2 (RV7P-01 fixed); RV8C-01 fixed in 11-b | yes |
| [21](21-unterminated-placeholder.md) | bug | an unterminated `[:` in a polymorphic FFI texture is dropped | yes, wrong output (a string literal containing `[:` printed without it) | `[` escaped (`\x5b`) in the string literal table | [21-a](patches/21-a-unterminated-placeholder.patch) | round 6 (RV6L-01) | yes |
| [24](24-matexp-state-order.md) | bug (non-reproducible builds) | the matrix-exponentiation pass orders a loop's state by heap addresses: equivalent but different code from run to run | no difference seen (no transformed loop in the lean2rr programs checked) | - | [24-a](patches/24-a-matexp-state-order.patch) | rv7/p22 round 2: deterministic, values unchanged | yes |
| [26](26-launder-assume.md) | bug (miscompile) | `assume(launder(p) == p)` undoes the launder, so LICM hoists the stores of a cell rebuilt in place | yes, wrong output (a Lean loop prints 2, natively 25009648) | none | fixed upstream (#651, `5776bbe5`; 26-a dropped) | rv8/reussir: no defect | upstream |
| [28](28-unique-carrying-join.md) | bug (miscompile) | `-O aggressive` proves a value unique that is shared on one path; the shared cell is updated in place | possible: not seen in lean2rr's corpus | none | [28-a](patches/28-a-unknown-absorbs-join.patch) | rv8/reussir/e (+ round 2): no correctness defect; RV8RE-01 (lost clones) fixed | yes |
| [29](29-ffi-member-mlir.md) | bug (tooling) | the `--emit mlir` dump of a record with an `#[ffi]` member does not parse back | no, builds unaffected; every lean2rr dump fails to parse | - | [29-a](patches/29-a-ffi-member-verifier.patch) | rv8/reussir/e: no defect | yes |
| [31](31-deep-expression-stack.md) | bug | rrc overflows its stack on deeply nested expressions | no, lean2rr bounds nesting | - | [31-a](patches/31-a-big-driver-stack.patch) | rv8/reussir/e (+ round 2): no correctness defect; RV8RE-02 (`ulimit -v`) fixed | yes |
| [33](33-rc-trailing-text.md) | bug (tooling) | the rc and ref type parser drops the text after a comma (`!reussir.rc<i64 rigid, atomic>` reads as `!reussir.rc<i64 rigid>`) | no, hand-written MLIR only | - | [33-a](patches/33-a-rc-type-closing-bracket.patch) | rv8/reussir/e/round2: no defect | yes |
| [43](43-nullable-as-ref.md) | bug | reussir-rt's `Nullable::as_ref` returns a reference to a local copy of the pointer word (dangling); `Nullable::new` checks the size only in debug builds | no: nothing calls it, and a `Nullable` cannot cross the FFI boundary | - | none | - | - |
| [44](44-small-allocation-limit.md) | bug (32-bit targets) | constant-size boxes of 513 to 1024 bytes go to `mi_malloc_small`, whose limit is 512 bytes there (heap corruption) | no: lean2rr builds only for 64-bit targets | - | none | - | - |
| [45](45-polyffi-rc-substitution.md) | bug (hand-written MLIR only) | a polymorphic-FFI substitution given as an MLIR rc type becomes Rust's `Rc` without the record's glue (members leak, immediates and atomic counts mishandled) | no: only hand-written MLIR gets there (the front end substitutes the text itself) | - | none | - | - |
| [47](47-unlink-provenance.md) | bug (latent UB; no miscompile seen) | reussir-rt's pending stack (`drop.rs`, from 13-b and 13-c; not upstream) rebuilds the pointer of a linked cell from the linking cell's pointer and an offset (`wrapping_offset`), so the pointer has the provenance of another, already freed allocation (Miri: undefined behaviour) | no wrong result seen (the release functions get the pointer through an indirect call), but many frees run the code | none | none of its own: fixed in [13-c](patches/13-c-cheaper-pending-stack.patch) (folded in on 2026-10-09; 13-c was never offered upstream) | fix checked (Miri, the same machine code); not reviewed yet | on `l2r-base2-47`; not yet on `l2r-base2` |
| [34](34-executable-textrel.md) | bug (link) | `rrc --emit executable` compiles static code but links a PIE: text relocations (GNU ld), a link error (lld, and on x86-64) | yes: every lean2rr binary has `DT_TEXTREL` on aarch64; with lld or on x86-64 it would not link | `l2r.py` passes `--relocation-mode pic` | [34-a](patches/34-a-pic-by-default.patch) | rv8/reussir/bug34: no defect | yes |
| [10](10-closure-type-print.md) | cost (build time) | closure devirtualization prints types exponentially | yes, build time and memory | `--no-closure-wpd` | [10-a](patches/10-a-closure-type-ids.patch) | rv7/p22 rounds 1-2 (RV7P-02, RV7P-04 fixed) | yes |
| [11](11-sccp-call-graph.md) | cost (stock MLIR pass; 11b: Reussir's own glue lookups) | interprocedural SCCP is superlinear; glue lookups rebuild a symbol table per call (11b) | yes, build time of large programs | none | [11-a](patches/11-a-sccp-call-budget.patch) (SCCP), [11-b](patches/11-b-glue-symbol-tables.patch) (11b) | rv8/reussir-c (RV8C-01, -02, -04 resolved) | yes |
| [16](16-nested-io-matches.md) | cost (opt-in flag) | reuse across calls is superlinear in match nesting (build time) | yes, build time and memory | deep tail paths and `let` values outlined | [16-a](patches/16-a-nested-if-token-free.patch) | rv8/reussir-c: no defect | yes |
| [17](17-long-nat-block.md) | cost (stock pass's default mode) | rrc memory is quadratic in a straight-line `Nat` function (`convert-scf-to-cf` with pattern rollback) | yes, build memory | long tail paths and `let` values outlined; `Array Nat` literals as tables | [17-a](patches/17-a-scf-to-cf-no-rollback.patch) | rv8/reussir-c: no defect | yes |
| [20](20-statet-tower.md) | cost (MLIR inliner; first unclear, cause found later) | the MLIR inliner follows chains of copied calls through recursive functions (build time) | yes, build time and memory | conversion, unboxing and uniform-code application functions marked `#[transform_anchor]` | [20-a](patches/20-a-no-inline-into-recursion.patch) | rv8/reussir-c: no defect | yes |
| [22](22-wildcard-wide-enum.md) | cost | a wildcard arm over a wide enum costs N^3 code | yes, build time (a derived BEq on 40 constructors: 9 minutes) | held wide values released out of line in wildcard arms (`l2r_sink`) | [22-a](patches/22-a-merge-wildcard-copies.patch) | rv8/reussir-c (RV8C-03 resolved) | yes |
| [23](23-polyffi-link.md) | cost (build time) | the compiled polymorphic-FFI modules are linked one call each, quadratic in their number | yes, build time (a Std.Http program with 8241 instances: 65 minutes of linking) | none | [23-a](patches/23-a-one-linker.patch) | RV6: no defect | yes |
| [25](25-value-record-dag.md) | cost (deliberate design) | the first acquire/drop expansion writes a `[value]` record's copy out in line, exponential for records shared in a DAG | no, lean2rr's `[value]` records are shallow | - | none | rv7/p22 round 2: agrees to leave it | - |
| [30](30-call-lowering-lookup.md) | cost (build time) | the call lowering scans the module once per call | yes, build time of large programs | none | [30-a](patches/30-a-callee-symbol-table.patch) | rv8/reussir/e: no defect (a latent hazard noted) | yes |
| [32](32-emit-mlir-size.md) | cost (debug output) | the `--emit mlir` dump is exponential in the nesting of records that share sub-records | no, builds unaffected; large programs cannot be dumped | dump smaller programs | none | - | - |
| [35](35-texture-rustc-runs.md) | cost (build time) | rrc compiles every polymorphic-FFI texture with rustc again on every build (about 470 per lean2rr program, 13 s of a small program's 16 s of rrc) | yes, build time | none needed: `l2r.py` sets `REUSSIR_FFI_CACHE_DIR` for 35-a's cache (ignored without the patch) | [35-a](patches/35-a-texture-cache.patch) | FCR (+ second look): FCR-01 (medium, a race) and the small findings fixed | yes |
| [3](03-global-alloc-align.md) | cost (run time; the 16-byte alignment itself is intended) | a Rust allocation whose size is not a multiple of 16 can be moved inside a larger mimalloc block: its page is marked, and every later free in it takes mimalloc's slow path | yes, speed (up to 5% of a program's instructions, varying from run to run) | the runtime allocates its own objects with `mi_malloc` | [03-a](patches/03-a-global-alloc-size-classes.patch), [03-b](patches/03-b-round-only-mimalloc.patch) (review fixes) | review-inline: F5-F7 (low) fixed in 03-b; second look pending | yes |
| [42](42-drop-run.md) | cost (run time) | a host frees one cell through the pending stack with a deferral and a drain: three calls, a push and a pop per freed cell | yes, speed (leanrt frees the last reference to a record or a boxed payload this way: about 5% of monadic-interp's instructions) | none possible (a host cannot start a drain itself) | none: the gain is too small for a local patch (owner, 2026-10-07); 42-a parked ([parked option](42-drop-run.md#parked-option-42-a)) | review-rtperf (42-a): correct; R42-01 to R42-03 (comments, a test gap) fixed | - |
| [7](07-phantom-reuse-donor.md) | missed optimization | token reuse picks decrements that never free | yes, speed | fields bound lazily (plan §5.5) | none (parked: [07-a](patches/parked/07-a-sink-bound-retains.patch)) | passed (revised after round 2); parked on 2026-10-07 | parked |
| [36](36-trampoline-inline.md) | missed optimization | a texture's import trampoline has no inline attribute: at a call site LLVM judges cold, a texture costing more than 45 stays a call | yes, speed (at a cold call site the read of a box from an `Array`, and of a `Nat` or `Int` element at its type, `RtReadsDeep`) | read textures kept small (the view protocol, perf-array-reads); `ffi-inline-check.sh` allows these three reads at `RtReadsDeep`'s cold call sites | none (parked: [36-a](patches/parked/36-a-inline-small-textures.patch), [36-b](patches/parked/36-b-inline-guards.patch)) | review-inline: F1 (high, a stack overflow) and F2-F4 fixed in 36-b; parked on 2026-10-07 | parked |
| [39](39-alias-release-donor.md) | missed optimization | token reuse takes the release of a value an opaque call returned (an alias of a live reference, so it never frees) as the donor, over the matched cell (equal score: the most recent producer wins) | no longer: it did with lean2rr commit 3f0cb30 (a field's own box passed back into a rebuilt node; `RtProbeBump`: one list cell for each rebuilt node), now reverted | avoided: a field put back into a rebuilt node is boxed again from its unboxed value | none | - | - |
| [13](13-long-list-drop.md) | missing feature | releasing a long list or a deep tree recurses once per cell | yes, stack overflow, 2x time and memory | none | [13-a](patches/13-a-release-chains-in-loop.patch), [13-b](patches/13-b-pending-release-stack.patch), [13-c](patches/13-c-cheaper-pending-stack.patch) (with the fix of issue 47 since 2026-10-09), [13-d](patches/13-d-last-field-order.patch) | 13-a passed (extended after round 2); 13-b passed (round 4, revised twice); 13-c passed (round 5); 13-d (13-b's release order, review RS11-01) passed (review-0069: no defect) | yes |
| [27](27-nullable-member-drop.md) | missing feature (a gap in issue 13's bounded-depth frees) | drop glue does not defer a `Nullable` member: a long chain through `Nullable` overflows the stack when freed | no, `Nullable` not used | - | [27-a](patches/27-a-defer-nullable-member.patch) (amended for RV8R-01) | rv7/p22 round 2 (RV7P-05); rv8/reussir: RV8R-01 fixed | yes |
| [38](38-tagged-top-bits.md) | missing feature | the inline count increment of a `tagged` handle uses all 64 bits as the address, so the top 16 bits cannot carry foreign data | yes: the one-word `Box` (`LAny`) needs it (`scripts/l2r.py` requires it) | none | [38-a](patches/38-a-tagged-top-bits.patch) | review-anybox r1: no defect (atomic test case added) | yes |
| [40](40-drain-end-hook.md) | missing feature | Reussir's runtime does not tell the host when a drain (a free) ends | yes: the `sync` dependents of a promise released inside a free must run when the free is over (`scripts/l2r.py` requires it) | none (a fallback until switch step 6) | [40-a](patches/40-a-drain-end-hook.patch) | rv8/reussir: no defect | yes |
| [41](41-tagged-ffi-objects.md) | missing feature | an opaque FFI handle must be a pointer to a counted box: it cannot be an immediate (a number) | yes: the one-word `Nat` and `Int` need it (the prelude declares them `tagged`) | none (before: `Nat` was a two-word `[value]` enum) | [41-a](patches/41-a-tagged-ffi-objects.patch) | the mem-nat review and rv8/nat: no defect | yes |
| [46](46-mimalloc-arena-purge.md) | issue (dependency: mimalloc v2.2.4, which reussir-rt pins through `libmimalloc-sys` 0.1.44) | mimalloc's delayed arena purges do not run (`src/arena.c:624` tests the purge time the wrong way round): freed huge blocks and segments stay in the process | yes, peak memory (lean-zip's benchmark: 422 MiB, 330 MiB with the workaround; native 394 MiB) | leanrt sets mimalloc's `arena_purge_mult` to 0 on v2.1.8 to v2.2.7 (`alloc::purge_arenas_at_once`) | none (a newer `libmimalloc-sys`, 0.1.49 or later, parked) | - | - |

**Counts.** 46 entries: 24 bugs, 13 costs, 3 missed optimizations, 5
missing features, 1 dependency issue. 30 entries have patches of their own in the series, 35
patch files in all (two each for entries 3 and 11, four for entry 13, one
each for the others); 5 entries are fixed upstream (4, 5, 9, 14 and 26:
their patches 04-a, 05-a, 09-a and 26-a dropped), and half of entry 2
(02-a dropped; 02-b, the variant half, stays); entry 47 has no patch of
its own: its fix is part of 13-c (since 2026-10-09); 10 entries have no
patch (7, 25, 32, 36, 39, 42, 43, 44, 45, 46). The 35 patches are 15 bug
fixes, 12 optimizations and 8 features (13-c, a feature, also has the fix
of bug 47); all 35 are on `l2r-base2-47`, and on `l2r-base2` with 13-c
before the fold. Five parked
patches lie outside the series and these counts
([parked patches](#parked-patches)).

Status words used in the entries' summaries:

- *worked around*: lean2rr avoids the construct or works around it.
- *patched*: a local patch fixes it, or for an issue that is not a bug,
  improves it.
- *does not affect lean2rr*: lean2rr never produces the triggering shape.
- *open*: lean2rr can hit it and has no fix or workaround.

## Applying the patches

[`patches/series`](patches/series) lists the patch files, one per line, in
the order to apply them. To make a patched Reussir, from the repository
root:

```sh
git -C reussir checkout -b l2r-base2 943f2195
while read -r p; do
    git -C reussir am "$PWD/reussir-bugs/patches/$p" || break
done < reussir-bugs/patches/series
cmake --build reussir/build
```

`git am` records the patches as local commits; `git apply` works as well,
if you would rather keep them as uncommitted changes. Checked on
2026-10-09 in a scratch worktree: the series on `943f2195` gives tree
`350be937`, the tree of `./reussir`'s `l2r-base2-47` (`b2e4a47e`). Until
then (13-c without the fix of issue 47) it gave tree `6d97d3d0`, the
tree of `l2r-base2` (`71f17ae2`; checked on 2026-10-07). The `From
<sha>` line of each patch file names its commit on `l2r-base2`, except
for 13-c and 40-a, whose files were made again from `l2r-base2-47` when
the fix of issue 47 was folded into 13-c (40-a's file for its moved
context: hunk line numbers and blob hashes). The other commits of
`l2r-base2-47` after 13-c were cherry-picked from `l2r-base2` without
conflicts, with the same changes and messages. The commits of
`l2r-base2` have the same messages and changes as those of `l2r-trim` and
`l2r-local` (the hashes of `l2r-local`'s commits are in each entry's
*Patch* section); only the context of 18-a and 11-a moved: upstream
added the archive `MLIRReussirIFRTJustInTimeTransform` next to their
lines in `lib/CAPI/CMakeLists.txt` and
`crates/reussir-backend-sys/build.rs`.

Until 2026-10-07 the base was `ef922049` and the series had 40 patches:
the 35 of today and, in this order, 04-a, 02-a, 09-a and 05-a after
06-a, and 26-a after 01-a. That series on ef922049 gave tree `a3f5b608`,
the tree of `l2r-trim` (`79c1d5f2`); its patch files, against ef922049,
are in this repository's history. Before that the series had 43
patches: 07-a after 02-a, 36-a after
13-d and 36-b after 03-a, and 09-a in its earlier form, which called a
helper of 07-a. That series on ef922049 gave tree `70f24fae`, the tree of
`l2r-local` and of the scratch Reussir branch `l2r-inline` (`136d9a9f`);
its first 41 patches gave tree `85ec7bd2` (`l2r-inline` at `ad079b37`,
before the review fixes of 36-a and 03-a); its first 39 patches gave
tree `560e017e`, the tree of the scratch Reussir branch `l2r-anybox`
(`1eb710b4`, d79f8b70 + 38-a + 13-d); its first 37 patches gave tree
`cececf25`, the tree of `l2r-local` d79f8b70 (2026-10-04 to 2026-10-06);
the four-digit files in their old order gave the same trees.

**Why the series is not in entry order.** The series is the order in which
the patches were made, reviewed and applied. Each patch applies on the
patches before it. An order by entry number would break dependencies: 01-a
needs 08-a, and 11-b must come after 19-a.

Order and dependencies:

- 13-b rewrites 13-a's code, and 13-c rewrites 13-b's runtime: 13-a, 13-b,
  13-c in that order. 13-d changes `emitCellRelease`, 13-b's code as 27-a
  amended it: it comes after 27-a. It was made on branch `l2r-anybox` of a
  Reussir worktree (`l2r-local` d79f8b70 plus 38-a) and touches none of
  38-a's files, so it applies on d79f8b70 alone too.
- 01-a needs 08-a: an arm's LLVM struct must fit in the payload, which
  needs the declaration-order layout to agree with Reussir's.
- 11-b must come after 19-a: it threads its symbol table collection
  through the member glue that 19-a's acquire glue creates (review
  RV8C-01). The patches from 22-a to 16-a in the series were rebased onto
  those from 08-a to 40-a (RV8C-02): 11-a and 20-a edit the archive list of
  `lib/CAPI/CMakeLists.txt` after 18-a.
- 12-a, 23-a, 28-a, 29-a, 30-a, 31-a and 33-a also apply alone (on
  ef922049, and on `943f2195`: `git apply --check`, 2026-10-07).
- 34-a (bug 34) was made on `l2r-final` cc8e5aa5 (the series up to 33-a),
  on branch `l2r-final-0065` of the local integration checkout; it applies
  after 33-a.
- 35-a (issue 35, a cost) was made on 34-a (branch `l2r-polyffi-cache` of
  a local Reussir build with the l2r-local patches applied) and touches
  none of 34-a's files, so it applies after 33-a or after 34-a.
- 38-a (issue 38) was made on `l2r-local` d79f8b70 (the series up to
  35-a).
- 03-a (issue 3, a cost) was made on the parked 36-a, on branch
  `l2r-inline` of a Reussir worktree. It changes only
  `crates/reussir-rt/src/alloc.rs`, which 36-a does not touch, and also
  applies on d79f8b70 and on ef922049 alone; in the series it comes after
  13-d.
- 03-b, the review fixes of 03-a, was made on the same branch after the
  parked 36-b (which touches none of its files). It needs 03-a and is the
  last line of the series.

What lean2rr needs: its runtime needs 13-b to build (`leanrt::drop` uses
`reussir_rt::drop`, the pending stack 13-b adds to Reussir's runtime);
`scripts/l2r.py` stops with an error when the Reussir checkout lacks 40-a,
38-a or 13-d (`REQUIRED_REUSSIR_PATCHES`); its prelude needs 41-a (it
declares `Nat` and `Int` `tagged`). `tests/runtime/ffi-inline-check.sh`
does not need the parked 36-a: at the cold call sites of `RtReadsDeep` it
allows the calls of the three read textures that cost more than LLVM's
cold-site threshold, the read of a box and the reads of a `Nat` or `Int`
element at its type ([issue 36](36-trampoline-inline.md)).
Without the other patches,
lean2rr programs still compile, but the bugs can appear (and the costs
come back).

**Adding a patch.** Name the file after its entry: `NN-x-slug.patch`, with
the next free letter of the entry (a new problem gets the next free entry
number, 48). Put it in `patches/` and add its name as the last line of
`patches/series`. Write the *Patch* and *Upstream note* sections of the
entry's file, and update the entry's row in the status table (column
*Applied*: "no" until it is on the Reussir branch named
[above](#reussir-issues-and-local-patches)). Add a row to the
[review table](#review) when its review is done.

### Parked patches

A parked patch was made and reviewed, but lean2rr's builds do not apply
it: the owner removed it from the series. Its file is in
[`patches/parked/`](patches/parked/), outside
[`patches/series`](patches/series) and the counts above; its entry says
why it is parked and describes the patch.

| Patch | Entry | Kind | Parked | Why |
|---|---|---|---|---|
| [07-a](patches/parked/07-a-sink-bound-retains.patch) | [7](07-phantom-reuse-donor.md) | optimization | 2026-10-07 | a missed optimization; lean2rr's `lazy-fields` covers it |
| [36-a](patches/parked/36-a-inline-small-textures.patch), [36-b](patches/parked/36-b-inline-guards.patch) (review fixes) | [36](36-trampoline-inline.md) | optimization | 2026-10-07 | the gain is too small for a local Reussir patch |
| [42-a](patches/parked/42-a-drop-run.patch) | [42](42-drop-run.md) | optimization | 2026-10-07 | the gain is too small for a local Reussir patch (about 5% of monadic-interp's instructions) |
| [03-c](patches/parked/03-c-natural-alignment.patch) | [3](03-global-alloc-align.md) | optimization | 2026-10-06 | an alternative to 03-a and 03-b that changes Reussir's rule of 16-byte alignment for Rust allocations; the owner kept the rule |

Their entries say "not patched" (03-c: issue 3 keeps 03-a and 03-b);
the issues stay open. The parked files are against the stacks they were
made on (ef922049 plus earlier patches of the series). On `l2r-base2`,
36-a with 36-b, 42-a and 03-c still apply (`git apply --check`,
2026-10-07); 07-a does not, since upstream's #653 adds the helper
`consumesFusedMember`, which 07-a also adds (as on `l2r-trim`, whose
09-a added it).

To park a patch of the series, move its file
to `patches/parked/`, delete its line from `patches/series`, rebuild the
Reussir stack from the series, and update the entry, its row and the
counts.

## Running the repros

[`repros/`](repros/) has one repro per entry: a plain Reussir program
(`bugNN-name.rr`), a Lean program built through lean2rr
(`bugNN-name.lean`) where the issue needs lean2rr's output, a small
generator (`bugNN-name.py`) where the program must be large, or a check
script (bugs 18 and 24), plus `bug07b-call-before-branch.rr`, a variant
used in issue 7's entry, and Rust tests of Reussir's runtime sources
(`bug43-nullable-as-ref.rs`; `bug47-unlink-provenance.rs`, which needs
Miri: its header gives the commands, and `run.sh` does not run it).
Entries 40 and 41 have no repro: they are
missing features that show only through a host that uses them, and their
patches carry their own tests. Entries 44 to 46 have none either: 44
needs a 32-bit target, 45 MLIR written by hand, and 46 is shown by
lean2rr's runtime test `RtArenaPurge` (its peak memory, through
`tests/runtime/alloc-check.sh`). Each repro file starts
with what it shows, the expected output and what Reussir ef922049 does
(47: what `l2r-base2` does, since its `drop.rs` comes from 13-b; and
that `l2r-base2-47`, with the fix, passes).

    reussir-bugs/repros/run.sh RRC_CHECKOUT [NN...]

builds each repro with `RRC_CHECKOUT/build/bin/rrc`, runs it and prints one
line per repro, `issue NN` and a status: `REPRODUCES` (the documented
behaviour: the bug or the cost), `FIXED` (the expected output or
measure), `OTHER` (something else), or `SKIPPED`
(a tool is missing, or a slow repro under `QUICK=1`), with what it saw
and, in brackets, the rrc flags. (Before 2026-10-05 the label was `bug
NN`; the recorded lines below and in the entries are shown with the
current label.) NN is an entry number (`1`, `02`, `13`, ...); the default
is every entry with a repro except 22, whose generator is run by hand,
and 47 (Miri, by hand).
`run.sh` alone prints its header: the options and the environment.

Issue 30's repro is an MLIR module timed through `reussir-opt` (`ninja -C
build reussir-opt`; SKIPPED when the checkout has not built it). The
script's header documents its environment (`WORK`, a scratch directory;
`RUSTC`; `QUICK=1`, which skips the slow repros 6, 10, 11, 16, 17, 20 and
23). The Lean repros (13 and 20, and the programs generated for 16 and 17)
need the toolchain `lean2rr/lean-toolchain` pins (`scripts/toolchain.sh`;
or `L2R_LEAN_TOOLCHAIN`) and a lean2rr build (`lake build` in `lean2rr/`).
The build-time repros (10, 11, 16, 17, 20, 23) take one to three minutes
each, and 16 and 20 need 1.2 to 3 GB (issue 20 without its patch); bug 6
runs for about 15 s.

A plain repro is built with

    rrc bugNN-name.rr -o bugNN --emit executable FLAGS \
        --polyffi-rust-path RUSTC --polyffi-libdir RT --polyffi-libdir RT/deps \
        --polyffi-libdir $(RUSTC --print target-libdir)

where RT is the checkout's `build/target-rt/release` and RUSTC the rustc
that built it (the polymorphic-FFI directories, as `scripts/l2r.py` passes
them). The entries show only `rrc FILE FLAGS`. "lean2rr's flags" are
`-O aggressive --no-pack-record-members --reuse-across-call`.

## Old patch numbers

Until 2026-10-06 the patch files were named `NNNN-l2r-local-...patch`, with
four-digit numbers: the early ones followed the bug numbers, the later
ones the order of creation, and 0040 and 0050 belonged to no entry.
Commit messages and older notes cite these numbers (also inside names
such as the branch `l2r-final-0065` or the review notes `review-0069`).
Old number, new name:

| Old | New | Old | New | Old | New |
|---|---|---|---|---|---|
| 0002 | 02-a (dropped: upstream) | 0019 | [02-b](patches/02-b-variant-field-store.patch) | 0034 | [20-a](patches/20-a-no-inline-into-recursion.patch) |
| 0004 | 04-a (dropped: upstream) | 0020 | [01-a](patches/01-a-value-enum-arm-bytes.patch) | 0035 | [16-a](patches/16-a-nested-if-token-free.patch) |
| 0005 | 05-a (dropped: upstream) | 0021 | 26-a (dropped: upstream) | 0040 | [40-a](patches/40-a-drain-end-hook.patch) |
| 0006 | [06-a](patches/06-a-immediate-count-wrap.patch) | 0022 | [15-a](patches/15-a-yield-parent-check.patch) | 0050 | [41-a](patches/41-a-tagged-ffi-objects.patch) |
| 0007 | [07-a](patches/parked/07-a-sink-bound-retains.patch) (parked) | 0023 | [19-a](patches/19-a-cell-value-record-glue.patch) | 0060 | [28-a](patches/28-a-unknown-absorbs-join.patch) |
| 0009 | 09-a (dropped: upstream) | 0024 | [10-a](patches/10-a-closure-type-ids.patch) | 0061 | [29-a](patches/29-a-ffi-member-verifier.patch) |
| 0012 | [12-a](patches/12-a-no-hash-node-cache.patch) | 0025 | [18-a](patches/18-a-archive-build-order.patch) | 0062 | [30-a](patches/30-a-callee-symbol-table.patch) |
| 0013 | [13-a](patches/13-a-release-chains-in-loop.patch) | 0026 | [24-a](patches/24-a-matexp-state-order.patch) | 0063 | [31-a](patches/31-a-big-driver-stack.patch) |
| 0014 | [13-b](patches/13-b-pending-release-stack.patch) | 0027 | [27-a](patches/27-a-defer-nullable-member.patch) | 0064 | [33-a](patches/33-a-rc-type-closing-bracket.patch) |
| 0015 | [13-c](patches/13-c-cheaper-pending-stack.patch) | 0030 | [22-a](patches/22-a-merge-wildcard-copies.patch) | 0065 | [34-a](patches/34-a-pic-by-default.patch) |
| 0016 | [21-a](patches/21-a-unterminated-placeholder.patch) | 0031 | [17-a](patches/17-a-scf-to-cf-no-rollback.patch) | 0066 | [35-a](patches/35-a-texture-cache.patch) |
| 0017 | [23-a](patches/23-a-one-linker.patch) | 0032 | [11-a](patches/11-a-sccp-call-budget.patch) | 0068 | [38-a](patches/38-a-tagged-top-bits.patch) |
| 0018 | [08-a](patches/08-a-padding-widening.patch) | 0033 | [11-b](patches/11-b-glue-symbol-tables.patch) | 0069 | [13-d](patches/13-d-last-field-order.patch) |

Ranges in old text cover the old numbers in between: "0013-0015" is
13-a to 13-c; "0018-0027" is the ten patches from 08-a to 27-a of the
series; "0030-0035" the six from 22-a to 16-a; "0060-0063" 28-a to 31-a.
The old number 0067 was reserved, with entry 37, for another track's
patch; there was no 0067 file.

## Policy

- Every Reussir problem lean2rr meets is documented here, with a repro.
- A real Reussir bug (verified reproducible erroneous behaviour) gets a
  small local patch, reviewed adversarially, even if lean2rr never
  triggers it or works around it.
- Only bug fixes and major items stay in the series (owner, 2026-10-07).
  Besides the bug fixes these are: the build-time costs that make large
  builds slow or infeasible (issues 10, 11, 16, 17, 20, 22, 23, 30, 35:
  optimizations, not fixes), the allocator fix that the owner chose
  (03-a and 03-b, issue 3, run time: they keep the intended alignment and
  remove the avoidable slow frees), and the features for missing features
  that lean2rr needs: 13-a to 13-d (issue 13), 27-a (issue 27, which
  extends issue 13's feature to `Nullable` members), 38-a, 40-a and 41-a.
- A patch that only buys a small run-time gain on a few programs is
  parked, not kept: 07-a (issue 7) and 36-a with 36-b (issue 36), both
  missed optimizations ([parked patches](#parked-patches)). Costs whose
  removal would be a redesign (25, 32) and missed optimizations stay
  unpatched, with the reason in their file.
- Patches are local: lean2rr's work never pushes or submits them. The
  "Upstream note" at the end of a patched entry is text for an upstream
  report. Five of the bug fixes are merged upstream (26-a, 02-a, 09-a,
  04-a and 05-a: pull requests #651 to #655, "fixed upstream" in the
  [status table](#status), and an *Upstream* line in each entry). The
  series dropped them when its base moved to `943f2195`, which includes
  them.
- lean2rr's workarounds stay, so that lean2rr also works with an unpatched
  Reussir. The exceptions are the features lean2rr requires
  ([what lean2rr needs](#applying-the-patches)): 13-b (the runtime does not
  build without it), 40-a, 38-a and 13-d (`scripts/l2r.py` stops with an
  error without them: `REQUIRED_REUSSIR_PATCHES`), and 41-a (the prelude
  declares `Nat` and `Int` `tagged`).

## Review

Each patch is reviewed adversarially: code review, differential fuzzing
against an independent reference evaluator, ASan builds (Miri for the
runtime patches), and lean2rr's runtime suite and corpus, in rounds
repeated until one finds nothing. The review notes cited as "round N,
finding X" or by finding IDs are local notes, outside this repository
(column *Notes*: their names):

| Patches | Round | Notes | Result |
|---|---|---|---|
| 02-a, 04-a, 05-a, 06-a, 07-a, 09-a, 12-a, 13-a | rounds 1 to 3 | `rv-patches/FINDINGS.txt`, `rv-patches/roundN/FINDINGS.txt` | passed (07-a, 09-a, 13-a revised) (07-a parked on 2026-10-07; 09-a in the helper-only form of upstream #653, the same code, from 2026-10-07; 02-a, 04-a, 05-a and 09-a merged upstream and dropped on 2026-10-07) |
| 13-b | round 4 (4, 4b, 4c) | `rv-patches/round4*/FINDINGS.txt` | passed, revised twice |
| 13-c | round 5 | `perf0014-review/` | passed |
| 21-a | lean2rr round 6 (RV6L-01) | `rv6/` | passed |
| 23-a | RV6 | `rv6/p17/FINDINGS.txt` | no defects |
| 08-a, 02-b, 01-a, 26-a, 27-a, 40-a | RV8 | `rv8/reussir/FINDINGS.txt` | no defect in 08-a, 02-b, 01-a, 26-a, 40-a; RV8R-01 (27-a, release order, low) fixed in the amended 27-a |
| 15-a, 19-a, 10-a, 18-a, 24-a | RV7-P22, rounds 1 and 2 | `rv7/p22/FINDINGS.txt`, `rv7/p22/round2/FINDINGS.txt` | RV7P-01 (19-a, exponential cell glue) and RV7P-02/04 (10-a, claims and docs) fixed; RV7P-03 became bug 24 (24-a), RV7P-05 issue 27 (27-a, a missing feature) |
| 22-a, 17-a, 11-a, 11-b, 20-a, 16-a | RV8C | `rv8/reussir-c/FINDINGS.txt` | RV8C-01 (11-b with 19-a, medium), -02 (conflicts), -03 (22-a, lost exact-size reuse), -04 (11-a, declarations counted) resolved in the final stack |
| 41-a | mem-nat review, RV8 | `mem/nat/review/FINDINGS.txt`, `rv8/nat/FINDINGS.txt` | no defect (the optional hardening is in) |
| 28-a, 29-a, 30-a, 31-a | RV8 (e) | `rv8/reussir/e/FINDINGS.txt` (its RV8E-NN cited as RV8RE-NN) | no correctness defect; RV8RE-01 (28-a: poison and tagged immediates blocked sound clones, low) and RV8RE-02 (31-a: panic under `ulimit -v`, low) fixed in the amended patches; a latent hazard of 30-a noted in issue 30 |
| 28-a, 31-a (amended), 33-a | RV8 (e) round 2 | `rv8/reussir/e/round2/FINDINGS.txt` | no defect: RV8RE-01/02 fixed; returning bottom for poison and tagged immediates checked sound in every position; 33-a rejects nothing rrc prints (four lean2rr dumps, about 5.3M rc types, re-read and re-printed byte-identically); the 31-a fallback keeps exit codes and messages under `ulimit -v` |
| 34-a | RV8 bug34 | `rv8/reussir/bug34/FINDINGS.txt` | no defect; N1: obj and staticlib outputs keep the static default (scope note); N2: the .text change is linker veneer padding |
| 35-a | FCR | `ffi-cache-review/` (repros) | no defect in single-build use; FCR-01 (medium: a library replaced during a run filed entries under the old key) fixed by stamping the hashed files; FCR-02 (`-L` kinds), FCR-03 (`%` in the directory), FCR-04 (say when caching is off), FCR-05 (bitcode magic) fixed; FCR-06/07 documentation; FCR-08 to FCR-10 lean2rr's documents; second look: the fixes sound, FCR2-01 (a package directory's stamp changed by unrelated entries) and FCR2-02 (in-place rewrite with the time put back: status-change time added) fixed |
| 38-a | review-anybox r1 | `review-anybox/r1` | no defect; the atomic case was added to the patch's test |
| 13-d | review-0069 | `review-0069/` | no defect |
| 36-a, 03-a | review-inline | `review-inline/` (repros: `stack/stack36.rr`, `v3/`, `cg/`) | F1 (36-a, high: `alwaysinline` skipped the inliner's stack limit for recursive callers; a stack overflow), F2 (36-a, low: textures that cannot return), F3 (36-a, hardening: interposable trampolines), F4 (36-a docs) fixed in 36-b; F5 (03-a, low: the rounding hid overflows from the sanitizers), F6 (03-a, low: the whole-block test under mimalloc v3), F7 (03-a docs) fixed in 03-b; a second look is pending for 03-b; 36-a and 36-b parked on 2026-10-07 |

The integration of the first 34 patches
(the local integration checkout, then at `5c0514e3`) was checked
with Reussir's lit suite (645 tests: 564 passed, 81 unsupported, none
failed), the classic corpus (18 programs, oracle checks all passed),
lean2rr's runtime tests and `run.sh` (below). The stack with the amended
28-a and 31-a and with 33-a (`cc8e5aa5`, the same tree as `l2r-local`
then): lit 647 tests, 566 passed, 81 unsupported, none failed;
LeanBoolLoop through lean2rr prints 25009648 (as native); the `.unique`
clones of the classic corpus are those the review expects (Mergesort 13,
Rbmap 5, Rbtree 5, TypeclassGeneric 16, the other 13 programs unchanged);
the review's six soundness probes print the right values; 10 lean2rr
runtime tests pass (RtFuzzReuse, RtFreshRebuildShared, RtShareMutators,
RtHashMap, RtDropDeep, RtNat, RtStack, RtJpShapes, RtPersistWalk,
RtStateMachines); `run.sh` as below.

**Audit (2026-10-02).** An independent review checked every entry then
known (1 to 20) against Reussir's own documentation, tests, design notes
and source, and against upstream `main` (one later commit, unrelated: none
of these is fixed upstream). The entries added since carry their own
verdicts. Its kinds are those [above](#kinds); for a bug its test was that
Reussir does something its own rules or tests say it should not. It also
had the verdict *unclear*: a real slowdown whose cause is not shown, which
issue 20 had until its cause was found (a cost). It called 10, 11b and 23
*bug (build time)*; they were reclassified as costs on 2026-10-05, since
their output is correct. Each entry's file starts with its kind (for an
issue that is not a bug, a line under the title says so), and its summary
with the audit's verdict where it gave one.

### Builds named in the entries

The repros were checked on these builds (on the aarch64 test machine):

- ef922049, unpatched (`./reussir` before `l2r-local`): every repro shows
  its issue.
- "the round-2 stack": ef922049 + 06-a, 04-a, 02-a, 07-a, 09-a, 05-a as
  they were in the second review round.
- "the revised 07-a/09-a": ef922049 + 07-a, 09-a, 05-a as revised after
  that review.
- "13-a, first version": the round-2 stack + 13-a, first version.
- "13-a, extended": ef922049 + 06-a, 04-a, 02-a, the revised 07-a/09-a,
  05-a + 13-a as extended for chains through a member that is not last,
  work in progress.
- ef922049 + 12-a.
- "the eight-patch set": ef922049 + 06-a, 04-a, 02-a, 07-a, 09-a, 05-a,
  13-a, 12-a as applied to `./reussir` (`l2r-local`, commit `42635042`)
  before 13-b. The third review round checked it.
- "the nine-patch set": the eight-patch set + 13-b.
- "the ten-patch set": the nine-patch set + 13-c (`l2r-local` until
  2026-10-03, now `l2r-local-pre-final`).
- `91da4f80`: the ten-patch set + 21-a + 23-a (a local checkout), the
  base on which every later patch up to 31-a in the series was made (in
  its first version), and the "without the patch" build of issues 17 and
  24 to 33. The amended 28-a and 31-a and 33-a were made on the final
  stack (`a75ed2cf`, then each other).
- "the final stack": ef922049 + the series up to 33-a (35 patches),
  `l2r-local` `cc8e5aa5` (the local integration checkout, the same tree).
  Before the review of 28-a to 31-a was folded in, it was 34 patches with
  the first versions of 28-a and 31-a (`5c0514e3`, kept in that checkout
  as branch `l2r-final-pre-e2`).
- `d79f8b70`: the final stack + 34-a + 35-a, `l2r-local` from 2026-10-04
  to 2026-10-06 (the first 37 patches of the series then).
- `1eb710b4`: d79f8b70 + 38-a + 13-d, branch `l2r-anybox` of a scratch
  Reussir worktree.
- `136d9a9f`: 1eb710b4 + 36-a, 03-a, 36-b, 03-b, branch `l2r-inline` of a
  scratch Reussir worktree, and `l2r-local` since 2026-10-07 (the series
  of 43 before 2026-10-07).
- `79c1d5f2`: `l2r-trim`, ef922049 + the series of 40 (2026-10-07: 07-a,
  36-a and 36-b parked, 09-a in its helper-only form).
- `71f17ae2`: `l2r-base2`, upstream `943f2195` + the series of 35
  (2026-10-07: 26-a, 02-a, 09-a, 04-a and 05-a merged upstream and
  dropped).
- `b2e4a47e`: `l2r-base2-47`, the series of 35 rebuilt on 2026-10-09
  with the fix of issue 47 folded into 13-c (`bd733417`); its tree
  differs from `71f17ae2`'s only in `drop.rs` and `drop/tests.rs`.

The unpatched `run.sh` lines quoted in the entries come from a recorded run
of the same script on unpatched ef922049, or, for entries 24 to 32, on
91da4f80.

### Latest recorded run

On the final stack, 2026-10-03, with a lean2rr build, from a scratch
directory (`run.sh` on the integration checkout, which has the same tree
as `./reussir`): every repro, then issue 17 again with its new measure
(below), and 24 to 27 once their repros were added. After 28-a and
31-a were amended and 33-a added (`cc8e5aa5`), every repro but the slow
ones (10, 11, 16, 17, 20, 23) was run again on that stack, with the same
statuses (03, 25 and 32 REPRODUCES, all others FIXED; the timing lines of
03 and 07 move within their noise); lines 28 to 33 are from that run.

    issue 01   FIXED       prints 42   [-O default]
    issue 02a  FIXED       prints 7005009   [-O aggressive --no-pack-record-members]
    issue 02b  FIXED       prints 5001   [-O aggressive]
    issue 03   REPRODUCES  Box<u64> 16-aligned: 1000 of 1000; mi_malloc(8) 16-aligned: 500 of 1000 alloc/free pairs: Box::new 0.159 s, mi_malloc 0.145 s, ratio 1.10   [-O aggressive]
    issue 04   FIXED       compiles, prints 1005   [-O aggressive]
    issue 05   FIXED       compiles, prints 3   [-O aggressive]
    issue 06   FIXED       N = 4294967300: prints 4294967300   [lean2rr's flags]
    issue 07   FIXED       insert returning t is 0.80x the rebuilding insert   [lean2rr's flags]
    issue 08   FIXED       prints 2550200000   [-O aggressive --no-pack-record-members]
    issue 09   FIXED       prints 0 (no wrong result in 1000 runs)   [lean2rr's flags]
    issue 10   FIXED       K = 20: 2.5 s with closure devirtualization, 2.1 s with --no-closure-wpd   [-O aggressive]
    issue 11   FIXED       N = 2000: 13.7 s, N = 4000: 23.4 s, N = 10: 1.6 s (1.80x without the fixed cost, for twice the call sites)   [-O aggressive]
    issue 12   FIXED       prints 424242   [-O aggressive]
    issue 13   FIXED       list, 1M cells, 8 MB stack: prints 1000000   [lean2rr's flags]
    issue 13   FIXED       snoc, 1M cells, 8 MB stack: prints 1000000   [lean2rr's flags]
    issue 13   FIXED       lspine, 1M cells, 8 MB stack: prints 1000000   [lean2rr's flags]
    issue 13   FIXED       lean2rr List.replicate, 40M cells, 1 GiB stack: prints (some 7)   [l2r.py]
    issue 13   FIXED       lean2rr snoc, 40M cells, 1 GiB stack: prints 0   [l2r.py]
    issue 14   FIXED       prints 0 (no wrong result in 1000 runs)   [lean2rr's flags]
    issue 15   FIXED       compiles, prints 1   [-O aggressive]
    issue 16   FIXED       rrc: N = 50: 35 s, 159 MB; N = 100: 39 s, 190 MB (1.18x memory); N = 100 without reuse across calls: 38 s, 183 MB   [l2r.py]
    issue 17   FIXED       rrc: N = 10: 140 MB; N = 250: 31 s, 337 MB; N = 500: 47 s, 556 MB (each let: 0.82 MB up to 250, 0.88 MB from 250 to 500, 1.07x)   [l2r.py]
    issue 18   FIXED       rrc-build depends on libMLIRReussirInstrumentNonlinearFFI.a
    issue 19   FIXED       compiles, prints 42   [-O aggressive]
    issue 20   FIXED       rrc: 78 s, 770 MB; with the conversion functions kept out of the inliner: 45 s, 217 MB (3.53x memory)   [l2r.py]
    issue 21   FIXED       prints 4   [-O aggressive]
    issue 23   FIXED       link of the gathered modules: K = 300: 0.9 s, K = 600: 1.0 s (1.11x for twice the instances)   [-O aggressive]
    issue 24   FIXED       12 runs of the order-6 recurrence: 1 output
    issue 25   REPRODUCES  --emit mlir-llvm: K = 8: 7341 lines, K = 10: 28875 lines (3.93x for two more levels)   [-O default]
    issue 26   FIXED       prints 25009648   [-O aggressive]
    issue 27   FIXED       1M links through Nullable, 8 MB stack: prints 1   [-O default]
    issue 28   FIXED       prints 101 1   [-O aggressive]
    issue 29   FIXED       the --emit mlir dump parses back and prints identically
    issue 30   FIXED       reussir-opt --reussir-convert-to-llvm: N = 5000: 0.5 s, N = 10000: 0.3 s (.60x for twice the calls)
    issue 31   FIXED       compiles, prints 32004007   [-O aggressive]
    issue 32   REPRODUCES  --emit mlir: K = 10: 2133 KB, K = 12: 8532 KB (3.99x for two more levels)
    issue 33   FIXED       rrc -x mlir rejects !reussir.rc<i64 rigid, atomic>: expected '>'
    issue 34   REPRODUCES  the executable needs text relocations (DT_TEXTREL); prints 6   [-O aggressive]

(`run.sh` prints lean2rr's flags in full; they are abbreviated here.) Every
patched entry shows FIXED. `03` (intended), `25` and `32` (costs, not
patched) show REPRODUCES, and `34`, whose patch 34-a was not applied then
(on `l2r-final-0065` the line reads `issue 34   FIXED       no text
relocations; prints 6`). Issue 35's repro came later (2026-10-04): on
`l2r-local` cc8e5aa5 `issue 35   REPRODUCES  second build: 3 of 3 textures
compiled again; both print 42`, on `l2r-polyffi-cache` (34-a and 35-a)
`issue 35   FIXED       second build: 0 of 3 textures compiled again; both
print 42`. Issue 38's repro came on 2026-10-06: on `l2r-local` d79f8b70
`issue 38   REPRODUCES  a tagged handle with top bits copied in line:
killed by SIGSEGV`, on `l2r-anybox` (d79f8b70 and 38-a) `issue 38
FIXED       a tagged handle with top bits copied in line: prints 143`.
Issue 39's repro came the same day: on `l2r-local` d79f8b70 and on
`l2r-anybox` 1eb710b4 (d79f8b70, 38-a, 13-d) `issue 39   REPRODUCES  bump
allocates 32020 cells for 1000 bumps, 129488 for 4000 (bump_b: 0, 0)`. On
`l2r-anybox` the same day, `issue 36   REPRODUCES  the cold call site
still calls the trampoline of mix; main's call is inlined` and, with 03's
repro rewritten to count the boxes moved inside a larger block instead of
timing allocations, `issue 03   REPRODUCES  Box<u64> 16-aligned: 1000 of
1000; mi_malloc(8) 16-aligned: 500 of 1000 boxes moved inside a larger
block: 500 of 1000`; on `l2r-inline` (36-a and 03-a) `issue 36   FIXED
both calls of mix inlined` and `issue 03   FIXED       Box<u64> 16-aligned: 1000 of 1000; mi_malloc(8)
16-aligned: 500 of 1000 boxes moved inside a larger block: 0 of 1000`. Two
lines changed with this run's script:

- **17.** The first version of the measure compared rrc's memory at
  N = 500 and N = 250 and called at most 1.6x linear; with 17-a it printed
  1.70x and 1.94x (`OTHER`). About 140 MB of rrc's memory does not depend
  on N, so a linear cost gives 1.7-1.9x. The line now compares the memory
  each further `let` costs (two runs: 1.07x and 1.19x with 17-a, 2.34x and
  2.41x without it); see [issue 17](17-long-nat-block.md#patch).
- **20.** It compares the build without lean2rr's anchors to the build
  with them: about 10x without 20-a (2.9 GB against 0.3 GB), 3.5x with
  it. The first thresholds (FIXED at most 1.5x) expected the anchors to
  stop mattering; the remaining 3.5x is the inliner's ordinary one-level
  inlining of the program's calls, which the anchors still avoid, and
  lean2rr keeps them. Now REPRODUCES at least 6x, FIXED at most 4.5x; see
  [issue 20](20-statet-tower.md#patch).

## Glossary

- **Cell** (or box): a heap object with a 32-bit reference count in its
  header. A *fused* variant box keeps the count and the variant tag in one
  8-byte header word.
- **Retain / release**: `reussir.rc.inc` / `reussir.rc.dec`. A release
  expands (`RcDecrementExpansion`) to "count == 1: drop the contents and
  keep the cell as a token; else count - 1".
- **Token reuse**: the cell freed by a release is offered as a *token* to a
  later allocation of the same size, so the construction writes into the
  old cell (Reussir's version of Lean's reset/reuse; pass `TokenReuse`).
  `--reuse-across-call` lets tokens live across non-tail calls.
- **Destructuring decrement**: a release of a match's scrutinee tagged by
  `RcDispatchFusion` with the arm's tag and the "bound" members. The
  members move to the arm's variables instead of being retained one by one.
  It is Koka's `dropn_reuse` shape.
- **Copy avoidance**: when a cell is reused, `RcCreateFusion` skips storing
  a field whose value is already in place (`skipFields`).
- **Drop glue**: the per-type functions that release a record's contents
  (`drop_in_place`, made by `AcquireDropExpansion`).
- **Immediates / TBI**: nullary constructors (`Nil`, `Leaf`) of shared
  enums are not allocated. Each is a tagged pointer to a static dummy box.
  TBI (aarch64's Top Byte Ignore) lets such a pointer carry the tag in its
  top byte and still be dereferenced.
- **Texture**: the Rust body of an `#[ffi(import)]` function; a polymorphic
  one is compiled by rustc once per instance.

## Other observations

- **Tagged pointers from the allocator.** Under top-byte tagging, a pointer
  with a nonzero top byte is an immediate. An allocator that tags real
  pointers (memory tagging, HWASan) would make real cells look like
  immediates: their decrements are skipped (a leak). The allocator lean2rr
  uses returns untagged pointers, and the sanitizer modes use the untagged
  encoding. Not reproducible on the test machine (no MTE). (Review round 1,
  RV-6; see [bug 6](06-static-count-wrap.md).)
- **Finalization order.** Values are not always released in the order of
  native Lean's `lean_del`. The difference is observable when releasing
  objects has effects, for example file handles that flush buffered output
  when dropped: 16 handles to one file kept in two lists printed `L7 L6 ...
  L0` natively and `L0 L1 ... L7` through lean2rr before patch 13-b. With
  13-b the order is Lean's in every free that starts at a container, and
  mostly below the first cell of a free that starts at a record; a list of
  handles dropped by itself closes `L0 L7 L6 … L1`, with lean2rr's one-word
  box `L0 L1 L7 … L2` (see "Order that still differs" in
  [issue 13](13-long-list-drop.md); plan §10).
- **Drop glue that may not return.** Reussir marks drop glue `mustprogress
  nounwind willreturn`. Through lean2rr's runtime (`leanrt::drop::run`,
  and the drain hook of [40-a](40-drain-end-hook.md)) a free can run Lean
  continuations, which might not return (`IO.Process.exit` inside a sync
  dependent), which would falsify `willreturn`. No concrete miscompile was
  found. (Review RV8, side note on 40-a.)
- **TokenReuse's locality bonus is dead code (not a bug).** A review of
  the patches from 22-a to 16-a pointed at
  `lib/Transformation/TokenReuse/TokenReuse.cpp`, function `heuristic`:
  walking from a new cell's field back to the cell it was loaded from, it
  steps from a dispatch arm's argument to `dispatch.getValue()`, the
  dispatch's *result*, where the scrutinee (`getVariant()`) is meant; for
  a dispatch without a result the next step reads a null value. The line
  never runs: the field list the walk starts from is read from
  `create.getRcPtr().getDefiningOp()`, the `rc.create` itself (its
  `getValue()` was meant), so the list is always empty. (Also, in rrc's
  pipeline the first `ConvertToSTD` lowers every `record.dispatch` before
  TokenReuse runs.) So the intended bonus for reusing the cell a new
  cell's fields come from never applies (a missed optimization: a donor
  scores 2 where the code means 4, a local probe `tv2.mlir`), and the
  crash is latent: with only the first mistake corrected, `reussir-opt
  --reussir-token-reuse` crashes (SIGSEGV) on a result-less dispatch (a
  local probe `tv3.mlir`, checked on a throwaway build). A fix needs both
  changes and would change which token is reused, a performance change;
  not patched. [Issue 39](39-alias-release-donor.md) is a case where the
  bonus would decide for the matched cell (the walk would then also have
  to step over `reussir.record.coerce`, the form an arm's field read has
  once `ConvertToSTD` has lowered the dispatch).

## Missing features that cost lean2rr performance

Not bugs, but each one costs lean2rr measurably:

- **Borrowed parameters.** Reads of arrays and strings through the runtime
  take the container owned, so each read retains and releases it.
  Traversals that keep unchanged nodes pay the same on fields (about 1.5x
  native on an `Expr.replace`-style DAG traversal).
- **A one-word `Nat`** (done locally: [issue 41](41-tagged-ffi-objects.md),
  patch 41-a, tagged opaque handles; `Nat` and `Int` are one tagged word,
  as natively; before, `Nat` was a two-word `[value]` enum and
  `Std.TreeMap Nat Nat` used about 1.5x native memory).
- **`[value]` types across the FFI.** Arrays of enumerations or `[value]`
  records need runtime-side representations or wrappers.
- **Guaranteed tail calls.** Mutual tail calls are sibling calls only when
  all arguments fit in registers.
