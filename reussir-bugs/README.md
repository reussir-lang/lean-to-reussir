# Reussir bugs met by lean2rr

Every Reussir problem lean2rr has run into, including those it works around
or never triggers. Each entry has one file, `NN-*.md`, with a repro, the
cause in Reussir's source where known, what lean2rr does about it, and, if
it is patched, the local patch explained, with its review. Most entries are
bugs; the audit below found a few that are intended behaviour, a missed
optimization, a missing feature, or build costs of a stock pass or an
opt-in flag (column *Kind*).

Reussir revision: `ef922049`. The checkout at `./reussir` is not part of
this repository; its branch `l2r-local` (head `cc8e5aa5`) is ef922049 plus
the 35 local patches, in the [apply list](#applying-the-patches)'s order.
(The `l2r-local` before 2026-10-03, the first twelve patches, is kept as
branch `l2r-local-pre-final`.)

- `NN-*.md`: one file per entry (status table below).
- [`patches/`](patches/): the local patches (`git format-patch` output
  against ef922049); [applying them](#applying-the-patches).
- [`local-additions.md`](local-additions.md): the two patches that fix no
  bug (0040, 0050).
- [`repros/`](repros/): the repro programs and `run.sh`, which builds and
  runs them; [running them](#running-the-repros).

## Policy

- Every Reussir problem lean2rr meets is documented here, with a repro.
- A real Reussir bug (verified reproducible erroneous behaviour) gets a
  small local patch, reviewed adversarially, even if lean2rr never
  triggers it or works around it.
- A build-time cost that comes from a fixable inefficiency gets a small
  patch too (bugs 11, 16, 17, 20, 22, 30, 35). Entries that are intended
  behaviour (3), costs whose fix would be a redesign (25, 32), or missed
  optimizations stay unpatched, with the reason in their file. Patches 0007
  (bug 7, an optimization that 0009 builds on) and 0013 to 0015 (bug 13, a
  missing feature lean2rr's runtime needs) predate this rule and stay, for
  the reasons in their files.
- Patches are local only: never pushed or submitted upstream. The
  "Upstream note" at the end of a patched entry is only text someone could
  use later.
- lean2rr's workarounds stay, so that lean2rr also works with an unpatched
  Reussir. The exception is bug 13: lean2rr's runtime needs 0014 to build.

## Status

Column *Patch*: "none" marks an entry that stays unpatched (the reason is
in its file). Column *Review*: the adversarial review round and its result
([Review](#review)). Column *Applied*: whether the patch is on
`./reussir`'s `l2r-local` (all 35 of the apply list are, since
2026-10-03; 0065 and 0066 are not yet).

| # | Kind | Effect | Affects lean2rr output? | lean2rr workaround | Patch | Review | Applied |
|---|---|---|---|---|---|---|---|
| [1](01-value-enum-payload.md) | bug | `[value]` enum payload bytes lost when a variant is moved | no, shape avoided | emits only unaffected `[value]` enums | 0020 | rv8/reussir: no defect | yes |
| [2](02-reuse-field-store.md) | bug | in-place reuse skips the store of a field that sits elsewhere in the new cell | structures: yes, wrong values; variants: no | variants: `--no-pack-record-members` and fields ordered by alignment | 0002 (structures), 0019 (variants) | 0002 passed (rounds 1-3); 0019 rv8/reussir: no defect | yes |
| [3](03-global-alloc-align.md) | intended | Rust allocations take mimalloc's aligned path | speed only | runtime calls `mi_malloc` itself | none | - | - |
| [4](04-recursive-type-compare.md) | bug | rrc recurses forever on two equal recursive types (SIGSEGV) | yes, rrc crash | driver retries without `--reuse-across-call` | 0004 | passed | yes |
| [5](05-one-armed-if.md) | bug | TokenReuse crashes on a one-armed `if` (SIGSEGV) | yes, rrc crash | prelude panics avoid the shape; user code can still hit it | 0005 | passed | yes |
| [6](06-static-count-wrap.md) | bug, with a flag workaround | a static cell is freed after about 2^32 references | yes, crash | `--nullary-variant-encoding arch-independent` or `boxed` (not used: 0006 keeps the default encoding's speed) | 0006 | passed | yes |
| [7](07-phantom-reuse-donor.md) | missed optimization | token reuse picks decrements that never free | yes, speed | fields bound lazily (plan §5.5) | 0007 | passed (revised after round 2) | yes |
| [8](08-padding-lift.md) | bug | padding "lift" gives LLVM a larger layout than Reussir's | no, shape never emitted | - | 0018 | rv8/reussir: no defect | yes |
| [9](09-duplicate-bound-member.md) | bug | a member used twice loses a reference (use after free) | yes, through Reussir's inliner | none | 0009 | passed (revised after round 2) | yes |
| [10](10-closure-type-print.md) | bug (build time) | closure devirtualization prints types exponentially | yes, build time and memory | `--no-closure-wpd` | 0024 | rv7/p22 rounds 1-2 (RV7P-02, RV7P-04 fixed) | yes |
| [11](11-sccp-call-graph.md) | cost (stock MLIR pass); 11b bug (build time) | interprocedural SCCP is superlinear; glue lookups rebuild a symbol table per call (11b) | yes, build time of large programs | none | 0032, 0033 | rv8/reussir-c (RV8C-01, -02, -04 resolved) | yes |
| [12](12-node-cache-collision.md) | bug (in cstree) | the parser swaps syntax subtrees whose hashes collide | yes, wrong code or bogus errors on very large files | none | 0012 | passed | yes |
| [13](13-long-list-drop.md) | missing feature | releasing a long list or a deep tree recurses once per cell | yes, stack overflow, 2x time and memory | none | 0013, 0014, 0015 | 0013 passed (extended after round 2); 0014 passed (round 4, revised twice); 0015 passed (round 5) | yes |
| [14](14-member-consumed-before-release.md) | bug | a member consumed before the release loses a reference (use after free) | yes, through Reussir's inliner | none | in 0009 | passed | yes |
| [15](15-nullable-match-yield.md) | bug | a `match` on a `Nullable` yielding a counted value does not compile | no, `Nullable` not used | - | 0022 | rv7/p22: no defect | yes |
| [16](16-nested-io-matches.md) | cost (opt-in flag) | reuse across calls is superlinear in match nesting (build time) | yes, build time and memory | deep tail paths and `let` values outlined | 0035 | rv8/reussir-c: no defect | yes |
| [17](17-long-nat-block.md) | cost (stock pass's default mode) | rrc memory is quadratic in a straight-line `Nat` function (`convert-scf-to-cf` with pattern rollback) | yes, build memory | long tail paths and `let` values outlined; `Array Nat` literals as tables | 0031 | rv8/reussir-c: no defect | yes |
| [18](18-rrc-target-deps.md) | bug (build system) | the `rrc` build target alone does not link | no, Reussir's build only | build the default target | 0025 | rv7/p22: no defect | yes |
| [19](19-cell-of-value-record.md) | bug | a `Cell` of a `[value]` record with counted members does not compile | yes, compile error | `[value]` records in references boxed (`Nat`/`Int` are tagged handles since 0050) | 0023 (with 0033's composition fix) | rv7/p22 rounds 1-2 (RV7P-01 fixed); RV8C-01 fixed in 0033 | yes |
| [20](20-statet-tower.md) | unclear, then found (MLIR inliner) | the MLIR inliner follows chains of copied calls through recursive functions (build time) | yes, build time and memory | conversion, unboxing and uniform-code application functions marked `#[transform_anchor]` | 0034 | rv8/reussir-c: no defect | yes |
| [21](21-unterminated-placeholder.md) | bug | an unterminated `[:` in a polymorphic FFI texture is dropped | yes, wrong output (a string literal containing `[:` printed without it) | `[` escaped (`\x5b`) in the string literal table | 0016 | round 6 (RV6L-01) | yes |
| [22](22-wildcard-wide-enum.md) | cost | a wildcard arm over a wide enum costs N^3 code | yes, build time (a derived BEq on 40 constructors: 9 minutes) | held wide values released out of line in wildcard arms (`l2r_sink`) | 0030 | rv8/reussir-c (RV8C-03 resolved) | yes |
| [23](23-polyffi-link.md) | bug (build time) | the compiled polymorphic-FFI modules are linked one call each, quadratic in their number | yes, build time (a Std.Http program with 8241 instances: 65 minutes of linking) | none | 0017 | RV6: no defect | yes |
| [24](24-matexp-state-order.md) | bug (non-reproducible builds) | the matrix-exponentiation pass orders a loop's state by heap addresses: equivalent but different code from run to run | no difference seen (no transformed loop in the lean2rr programs checked) | - | 0026 | rv7/p22 round 2: deterministic, values unchanged | yes |
| [25](25-value-record-dag.md) | cost (deliberate design) | the first acquire/drop expansion writes a `[value]` record's copy out in line, exponential for records shared in a DAG | no, lean2rr's `[value]` records are shallow | - | none | rv7/p22 round 2: agrees to leave it | - |
| [26](26-launder-assume.md) | bug (miscompile) | `assume(launder(p) == p)` undoes the launder, so LICM hoists the stores of a cell rebuilt in place | yes, wrong output (a Lean loop prints 2, natively 25009648) | none | 0021 | rv8/reussir: no defect | yes |
| [27](27-nullable-member-drop.md) | missing feature (a gap in bug 13's bounded-depth frees) | drop glue does not defer a `Nullable` member: a long chain through `Nullable` overflows the stack when freed | no, `Nullable` not used | - | 0027 (amended for RV8R-01) | rv7/p22 round 2 (RV7P-05); rv8/reussir: RV8R-01 fixed | yes |
| [28](28-unique-carrying-join.md) | bug (miscompile) | `-O aggressive` proves a value unique that is shared on one path; the shared cell is updated in place | possible: not seen in lean2rr's corpus | none | 0060 | rv8/reussir/e (+ round 2): no correctness defect; RV8RE-01 (lost clones) fixed | yes |
| [29](29-ffi-member-mlir.md) | bug (tooling) | the `--emit mlir` dump of a record with an `#[ffi]` member does not parse back | no, builds unaffected; every lean2rr dump fails to parse | - | 0061 | rv8/reussir/e: no defect | yes |
| [30](30-call-lowering-lookup.md) | cost (build time) | the call lowering scans the module once per call | yes, build time of large programs | none | 0062 | rv8/reussir/e: no defect (a latent hazard noted) | yes |
| [31](31-deep-expression-stack.md) | bug | rrc overflows its stack on deeply nested expressions | no, lean2rr bounds nesting | - | 0063 | rv8/reussir/e (+ round 2): no correctness defect; RV8RE-02 (`ulimit -v`) fixed | yes |
| [32](32-emit-mlir-size.md) | cost (debug output) | the `--emit mlir` dump is exponential in the nesting of records that share sub-records | no, builds unaffected; large programs cannot be dumped | dump smaller programs | none | - | - |
| [33](33-rc-trailing-text.md) | bug (tooling) | the rc and ref type parser drops the text after a comma (`!reussir.rc<i64 rigid, atomic>` reads as `!reussir.rc<i64 rigid>`) | no, hand-written MLIR only | - | 0064 | rv8/reussir/e/round2: no defect | yes |
| [34](34-executable-textrel.md) | bug (link) | `rrc --emit executable` compiles static code but links a PIE: text relocations (GNU ld), a link error (lld, and on x86-64) | yes: every lean2rr binary has `DT_TEXTREL` on aarch64; with lld or on x86-64 it would not link | `l2r.py` passes `--relocation-mode pic` | 0065 | rv8/reussir/bug34: no defect | no |
| [35](35-texture-rustc-runs.md) | cost (build time) | rrc compiles every polymorphic-FFI texture with rustc again on every build (about 470 per lean2rr program, 13 s of a small program's 16 s of rrc) | yes, build time | none needed: `l2r.py` sets `REUSSIR_FFI_CACHE_DIR` for 0066's cache (ignored without the patch) | 0066 | FCR (+ second look): FCR-01 (medium, a race) and the small findings fixed | no |

In numbers: 35 entries. 32 are patched by 35 patches (0013 to 0015 for
bug 13, 0002 and 0019 for bug 2, 0032 and 0033 for bug 11; 0009 fixes
bugs 9 and 14), all applied but 0065 (bug 34) and 0066 (bug 35), not yet
applied; 3 stay
documented only: 3 (intended), 25 and 32 (costs). The two other patches, 0040 and 0050, fix no bug
([local additions](local-additions.md)). Reviews: every patch passed its
round; 0066's round (FCR) found a race, fixed and checked by a second look.

Status words used in the entries' summaries:

- *worked around*: lean2rr avoids the construct or works around it.
- *patched*: a local patch fixes it (all patches are applied).
- *does not affect lean2rr*: lean2rr never produces the triggering shape.
- *open*: lean2rr can hit it and has no fix or workaround.

## Local additions

[`local-additions.md`](local-additions.md) describes the two patches that
fix no bug:

- **0040**, a hook at the end of a drain (`__reussir_drop_drained`):
  `reussir_rt::drop` calls a function the host stores when a drain that
  released something ends. lean2rr's runtime uses it to run the `sync`
  dependents of a promise released inside a free the record glue starts
  (it links the symbol weakly, so it also builds without the patch).
- **0050**, tagged opaque handles: `#[ffi(rust = "...", tagged)]` makes an
  odd handle an immediate that is not counted. lean2rr's one-word `Nat` and
  `Int` (merged from branch `mem-nat`) need it.

## Applying the patches

`./reussir`'s local branch `l2r-local` (never pushed) is ef922049 plus the
35 patches, as local commits, applied in the order of the `for` list below
(the apply list). To recreate it, from the repository root:

```sh
git -C reussir checkout -b l2r-local ef922049
for p in 0006 0004 0002 0007 0009 0005 0013 0012 0014 0015 0016 0017 \
         0018 0019 0020 0021 0022 0023 0024 0025 0026 0027 0040 \
         0030 0031 0032 0033 0034 0035 0050 0060 0061 0062 0063 0064; do
    git -C reussir am "$PWD/reussir-bugs/patches/$p-"*.patch || break
done
cmake --build reussir/build
```

`git am` records them as local commits; `git apply` works as well, if you
would rather keep them as uncommitted changes. Applied this way to
ef922049 (in a scratch worktree, 2026-10-03), the list gives exactly the
tree of `./reussir`'s `l2r-local` (`cc8e5aa5`). The `From <sha>` line of
each patch file names the commit of the integration checkout
(a local integration checkout); `l2r-local`'s commits have the
same contents and messages (their hashes are in each entry's *Patch*
section).

Order and dependencies:

- 0009 needs 0007: it calls `consumesFusedMember`, which 0007 adds.
- 0014 rewrites 0013's code, and 0015 rewrites 0014's runtime: 0013, 0014,
  0015 in that order.
- 0020 needs 0018: an arm's LLVM struct must fit in the payload, which
  needs the declaration-order layout to agree with Reussir's.
- 0033 must come after 0023: it threads its symbol table collection
  through the member glue that 0023's acquire glue creates (review
  RV8C-01). 0030 to 0035 were rebased onto 0018-0027 and 0040 (RV8C-02):
  0032 and 0034 edit the archive list of `lib/CAPI/CMakeLists.txt` after
  0025.
- 0012, 0017 and 0060 to 0064 also apply alone.
- 0065 (bug 34) is not on the list yet: it was made on `l2r-final`
  cc8e5aa5 (the list above) and is on branch `l2r-final-0065` of the
  local integration checkout; it applies after 0064.
- 0066 (bug 35) is not on the list yet: it was made on 0065 (branch
  `l2r-polyffi-cache` of a local Reussir build with the l2r-local patches
  applied) and
  touches none of 0065's files, so it applies after 0064 or after 0065.
- lean2rr's runtime needs 0014 to build (`leanrt::drop` uses
  `reussir_rt::drop`, the pending stack 0014 adds to Reussir's runtime),
  uses 0040 when present (a weak symbol), and its prelude needs 0050
  (it declares `Nat` and `Int` `tagged`).
  Without the others, lean2rr programs still compile, but the bugs can
  appear.

**Adding a patch:** put the file in `patches/`, write the *Patch* and
*Upstream note* sections of the entry's file, update the entry's row in the
status table, and, once it is applied to `l2r-local`, add it to the apply
list.

## Running the repros

[`repros/`](repros/) has one repro per entry: a plain Reussir program (`bugNN-name.rr`), a Lean program built through
lean2rr (`bugNN-name.lean`) where the bug needs lean2rr's output, a small
generator (`bugNN-name.py`) where the program must be large, or a check
script (bugs 18 and 24), plus `bug07b-call-before-branch.rr`, a variant
used in bug 7's entry. Each file starts with what it shows, the expected
output and what Reussir ef922049 does.

    reussir-bugs/repros/run.sh RRC_CHECKOUT [BUG...]

builds each repro with `RRC_CHECKOUT/build/bin/rrc`, runs it and prints one
line per repro: `REPRODUCES` (the documented bad behaviour), `FIXED` (the
expected output), `OTHER` (something else), or `SKIPPED` (a tool is
missing, or a slow repro under `QUICK=1`), with what it saw and, in
brackets, the rrc flags. BUG is a number (`1`, `02`, `13`, ...); the
default is every entry except 22, whose generator is run by hand. Bug 30's
repro is an MLIR module timed through `reussir-opt` (`ninja -C build
reussir-opt`; SKIPPED when the checkout has not built it). The script's
header documents its environment (`WORK`, a scratch directory; `RUSTC`;
`QUICK=1`, which skips the slow repros 6, 10, 11, 16, 17, 20 and 23). The
Lean repros (13 and 20, and the programs generated for 16 and 17) need
the toolchain `lean2rr/lean-toolchain` pins (`scripts/toolchain.sh`; or
`L2R_LEAN_TOOLCHAIN`) and a lean2rr build (`lake build` in `lean2rr/`). The
build-time repros (10, 11, 16, 17, 20, 23) take one to three minutes each,
and 16 and 20 need 1.2 to 3 GB (bug 20 without its patch); bug 6 runs for
about 15 s.

A plain repro is built with

    rrc bugNN-name.rr -o bugNN --emit executable FLAGS \
        --polyffi-rust-path RUSTC --polyffi-libdir RT --polyffi-libdir RT/deps \
        --polyffi-libdir $(RUSTC --print target-libdir)

where RT is the checkout's `build/target-rt/release` and RUSTC the rustc
that built it (the polymorphic-FFI directories, as `scripts/l2r.py` passes
them). The entries show only `rrc FILE FLAGS`. "lean2rr's flags" are
`-O aggressive --no-pack-record-members --reuse-across-call`.

### Builds named in the entries

The repros were checked on these builds (on the aarch64 test machine):

- ef922049, unpatched (`./reussir` before `l2r-local`): every repro shows
  its bug.
- "the round-2 stack": ef922049 + 0006, 0004, 0002, 0007, 0009, 0005 as
  they were in the second review round.
- "the revised 0007/0009": ef922049 + 0007, 0009, 0005 as revised after
  that review.
- "0013, first version": the round-2 stack + 0013, first version.
- "0013, extended": ef922049 + 0006, 0004, 0002, the revised 0007/0009,
  0005 + 0013 as extended for chains through a member that is not last,
  work in progress.
- ef922049 + 0012.
- "the eight-patch set": ef922049 + 0006, 0004, 0002, 0007, 0009, 0005,
  0013, 0012 as applied to `./reussir` (`l2r-local`, commit `42635042`)
  before 0014. The third review round checked it.
- "the nine-patch set": the eight-patch set + 0014.
- "the ten-patch set": the nine-patch set + 0015 (`l2r-local` until
  2026-10-03, now `l2r-local-pre-final`).
- `91da4f80`: the ten-patch set + 0016 + 0017
  (a local checkout), the base every later patch
  (0018 to 0063, in their first versions) was made on, and the "without
  the patch" build of bugs 17 and 24 to 33. The amended 0060 and 0063 and
  0064 were made on the final stack (`a75ed2cf`, then each other).
- "the final stack": ef922049 + the 35 patches, `l2r-local` `cc8e5aa5`
  (the local integration checkout, the same tree). Before the
  review of 0060 to 0063 was folded in, it was 34 patches with the first
  versions of 0060 and 0063 (`5c0514e3`, kept in that checkout as
  branch `l2r-final-pre-e2`).

The unpatched `run.sh` lines quoted in the entries come from a recorded run
of the same script on unpatched ef922049, or, for entries 24 to 32, on
91da4f80.

### Latest recorded run

On the final stack, 2026-10-03, with a lean2rr build, from a scratch
directory (`run.sh` on the integration checkout, which has the same tree
as `./reussir`): every repro, then bug 17 again with its new measure
(below), and 24 to 27 once their repros were added. After 0060 and
0063 were amended and 0064 added (`cc8e5aa5`), every repro but the slow
ones (10, 11, 16, 17, 20, 23) was run again on that stack, with the same
statuses (03, 25 and 32 REPRODUCES, all others FIXED; the timing lines of
03 and 07 move within their noise); lines 28 to 33 are from that run.

    bug 01   FIXED       prints 42   [-O default]
    bug 02a  FIXED       prints 7005009   [-O aggressive --no-pack-record-members]
    bug 02b  FIXED       prints 5001   [-O aggressive]
    bug 03   REPRODUCES  Box<u64> 16-aligned: 1000 of 1000; mi_malloc(8) 16-aligned: 500 of 1000 alloc/free pairs: Box::new 0.159 s, mi_malloc 0.145 s, ratio 1.10   [-O aggressive]
    bug 04   FIXED       compiles, prints 1005   [-O aggressive]
    bug 05   FIXED       compiles, prints 3   [-O aggressive]
    bug 06   FIXED       N = 4294967300: prints 4294967300   [lean2rr's flags]
    bug 07   FIXED       insert returning t is 0.80x the rebuilding insert   [lean2rr's flags]
    bug 08   FIXED       prints 2550200000   [-O aggressive --no-pack-record-members]
    bug 09   FIXED       prints 0 (no wrong result in 1000 runs)   [lean2rr's flags]
    bug 10   FIXED       K = 20: 2.5 s with closure devirtualization, 2.1 s with --no-closure-wpd   [-O aggressive]
    bug 11   FIXED       N = 2000: 13.7 s, N = 4000: 23.4 s, N = 10: 1.6 s (1.80x without the fixed cost, for twice the call sites)   [-O aggressive]
    bug 12   FIXED       prints 424242   [-O aggressive]
    bug 13   FIXED       list, 1M cells, 8 MB stack: prints 1000000   [lean2rr's flags]
    bug 13   FIXED       snoc, 1M cells, 8 MB stack: prints 1000000   [lean2rr's flags]
    bug 13   FIXED       lspine, 1M cells, 8 MB stack: prints 1000000   [lean2rr's flags]
    bug 13   FIXED       lean2rr List.replicate, 40M cells, 1 GiB stack: prints (some 7)   [l2r.py]
    bug 13   FIXED       lean2rr snoc, 40M cells, 1 GiB stack: prints 0   [l2r.py]
    bug 14   FIXED       prints 0 (no wrong result in 1000 runs)   [lean2rr's flags]
    bug 15   FIXED       compiles, prints 1   [-O aggressive]
    bug 16   FIXED       rrc: N = 50: 35 s, 159 MB; N = 100: 39 s, 190 MB (1.18x memory); N = 100 without reuse across calls: 38 s, 183 MB   [l2r.py]
    bug 17   FIXED       rrc: N = 10: 140 MB; N = 250: 31 s, 337 MB; N = 500: 47 s, 556 MB (each let: 0.82 MB up to 250, 0.88 MB from 250 to 500, 1.07x)   [l2r.py]
    bug 18   FIXED       rrc-build depends on libMLIRReussirInstrumentNonlinearFFI.a
    bug 19   FIXED       compiles, prints 42   [-O aggressive]
    bug 20   FIXED       rrc: 78 s, 770 MB; with the conversion functions kept out of the inliner: 45 s, 217 MB (3.53x memory)   [l2r.py]
    bug 21   FIXED       prints 4   [-O aggressive]
    bug 23   FIXED       link of the gathered modules: K = 300: 0.9 s, K = 600: 1.0 s (1.11x for twice the instances)   [-O aggressive]
    bug 24   FIXED       12 runs of the order-6 recurrence: 1 output
    bug 25   REPRODUCES  --emit mlir-llvm: K = 8: 7341 lines, K = 10: 28875 lines (3.93x for two more levels)   [-O default]
    bug 26   FIXED       prints 25009648   [-O aggressive]
    bug 27   FIXED       1M links through Nullable, 8 MB stack: prints 1   [-O default]
    bug 28   FIXED       prints 101 1   [-O aggressive]
    bug 29   FIXED       the --emit mlir dump parses back and prints identically
    bug 30   FIXED       reussir-opt --reussir-convert-to-llvm: N = 5000: 0.5 s, N = 10000: 0.3 s (.60x for twice the calls)
    bug 31   FIXED       compiles, prints 32004007   [-O aggressive]
    bug 32   REPRODUCES  --emit mlir: K = 10: 2133 KB, K = 12: 8532 KB (3.99x for two more levels)
    bug 33   FIXED       rrc -x mlir rejects !reussir.rc<i64 rigid, atomic>: expected '>'
    bug 34   REPRODUCES  the executable needs text relocations (DT_TEXTREL); prints 6   [-O aggressive]

(`run.sh` prints lean2rr's flags in full; they are abbreviated here.) Every
patched entry shows FIXED. `03` (intended), `25` and `32` (costs, not
patched) show REPRODUCES, and `34`, whose patch 0065 is not applied yet
(on `l2r-final-0065` the line reads `bug 34   FIXED       no text
relocations; prints 6`). Bug 35's repro came later (2026-10-04): on
`l2r-local` cc8e5aa5 `bug 35   REPRODUCES  second build: 3 of 3 textures
compiled again; both print 42`, on `l2r-polyffi-cache` (0065 and 0066)
`bug 35   FIXED       second build: 0 of 3 textures compiled again; both
print 42`. Two lines changed with this run's script:

- **17.** The first version of the measure compared rrc's memory at
  N = 500 and N = 250 and called at most 1.6x linear; with 0031 it printed
  1.70x and 1.94x (`OTHER`). About 140 MB of rrc's memory does not depend
  on N, so a linear cost gives 1.7-1.9x. The line now compares the memory
  each further `let` costs (two runs: 1.07x and 1.19x with 0031, 2.34x and
  2.41x without it); see [bug 17](17-long-nat-block.md#patch).
- **20.** It compares the build without lean2rr's anchors to the build
  with them: about 10x without 0034 (2.9 GB against 0.3 GB), 3.5x with
  it. The first thresholds (FIXED at most 1.5x) expected the anchors to
  stop mattering; the remaining 3.5x is the inliner's ordinary one-level
  inlining of the program's calls, which the anchors still avoid, and
  lean2rr keeps them. Now REPRODUCES at least 6x, FIXED at most 4.5x; see
  [bug 20](20-statet-tower.md#patch).

## Review

Each patch is reviewed adversarially: code review, differential fuzzing
against an independent reference evaluator, ASan builds (Miri for the
runtime patches), and lean2rr's runtime suite and corpus, in rounds
repeated until one finds nothing. The review notes cited as "round N,
finding X" or by finding IDs are local notes, outside this repository
(column *Notes*: their names):

| Patches | Round | Notes | Result |
|---|---|---|---|
| 0002, 0004-0007, 0009, 0012, 0013 | rounds 1 to 3 | `rv-patches/FINDINGS.txt`, `rv-patches/roundN/FINDINGS.txt` | passed (0007, 0009, 0013 revised) |
| 0014 | round 4 (4, 4b, 4c) | `rv-patches/round4*/FINDINGS.txt` | passed, revised twice |
| 0015 | round 5 | `perf0014-review/` | passed |
| 0016 | lean2rr round 6 (RV6L-01) | `rv6/` | passed |
| 0017 | RV6 | `rv6/p17/FINDINGS.txt` | no defects |
| 0018-0021, 0027, 0040 | RV8 | `rv8/reussir/FINDINGS.txt` | no defect in 0018-0021, 0040; RV8R-01 (0027, release order, low) fixed in the amended 0027 |
| 0022-0026 | RV7-P22, rounds 1 and 2 | `rv7/p22/FINDINGS.txt`, `rv7/p22/round2/FINDINGS.txt` | RV7P-01 (0023, exponential cell glue) and RV7P-02/04 (0024, claims and docs) fixed; RV7P-03 became bug 24 (0026), RV7P-05 bug 27 (0027) |
| 0030-0035 | RV8C | `rv8/reussir-c/FINDINGS.txt` | RV8C-01 (0033 with 0023, medium), -02 (conflicts), -03 (0030, lost exact-size reuse), -04 (0032, declarations counted) resolved in the final stack |
| 0050 | mem-nat review, RV8 | `mem/nat/review/FINDINGS.txt`, `rv8/nat/FINDINGS.txt` | no defect (the optional hardening is in) |
| 0060-0063 | RV8 (e) | `rv8/reussir/e/FINDINGS.txt` (its RV8E-NN cited as RV8RE-NN) | no correctness defect; RV8RE-01 (0060: poison and tagged immediates blocked sound clones, low) and RV8RE-02 (0063: panic under `ulimit -v`, low) fixed in the amended patches; a latent hazard of 0062 noted in bug 30 |
| 0060, 0063 (amended), 0064 | RV8 (e) round 2 | `rv8/reussir/e/round2/FINDINGS.txt` | no defect: RV8RE-01/02 fixed; returning bottom for poison and tagged immediates checked sound in every position; 0064 rejects nothing rrc prints (four lean2rr dumps, about 5.3M rc types, re-read and re-printed byte-identically); the 0063 fallback keeps exit codes and messages under `ulimit -v` |
| 0065 | RV8 bug34 | `rv8/reussir/bug34/FINDINGS.txt` | no defect; N1: obj and staticlib outputs keep the static default (scope note); N2: the .text change is linker veneer padding |
| 0066 | FCR | `ffi-cache-review/` (repros) | no defect in single-build use; FCR-01 (medium: a library replaced during a run filed entries under the old key) fixed by stamping the hashed files; FCR-02 (`-L` kinds), FCR-03 (`%` in the directory), FCR-04 (say when caching is off), FCR-05 (bitcode magic) fixed; FCR-06/07 documentation; FCR-08 to FCR-10 lean2rr's documents; second look: the fixes sound, FCR2-01 (a package directory's stamp changed by unrelated entries) and FCR2-02 (in-place rewrite with the time put back: status-change time added) fixed |

The integration of the first 34 patches
(the local integration checkout, then at `5c0514e3`) was checked
with Reussir's lit suite (645 tests: 564 passed, 81 unsupported, none
failed), the classic corpus (18 programs, oracle checks all passed),
lean2rr's runtime tests and `run.sh` (above). The stack with the amended
0060 and 0063 and with 0064 (`cc8e5aa5`, the same tree as `l2r-local`):
lit 647 tests, 566 passed, 81 unsupported, none failed; LeanBoolLoop
through lean2rr prints 25009648 (as native); the `.unique` clones of the
classic corpus are those the review expects (Mergesort 13, Rbmap 5, Rbtree
5, TypeclassGeneric 16, the other 13 programs unchanged); the review's
six soundness probes print the right values; 10 lean2rr runtime tests
pass (RtFuzzReuse, RtFreshRebuildShared, RtShareMutators, RtHashMap,
RtDropDeep, RtNat, RtStack, RtJpShapes, RtPersistWalk, RtStateMachines);
`run.sh` as above.

**Audit (2026-10-02).** An independent review checked every entry then
known (1 to 20) against Reussir's own documentation, tests, design notes
and source, and against upstream `main` (one later commit, unrelated: none
of these is fixed upstream). The entries added since carry their own
verdicts. Kinds:

- *bug*: Reussir does something its own rules or tests say it should not;
- *intended*: documented behaviour;
- *missed optimization*: correct output, slower than it could be;
- *missing feature*: something Reussir never promised (here: bounded-depth
  frees) that Lean's semantics need;
- *cost*: build time or memory of a stock pass, an opt-in flag or a
  deliberate design, not a defect;
- *unclear*: a real slowdown whose cause is not shown.

Each entry's summary starts with its kind, and with the audit's verdict
where it gave one. Of the patches, by their entries' kinds:

- bugs: 0002 and 0019 (2), 0004, 0005, 0009 (9 and 14), 0012 (in Reussir's
  parser dependency `cstree`), 0016 (21), 0017 (23), 0018 (8), 0020 (1),
  0021 (26), 0022 (15), 0023 (19), 0024 (10), 0025 (18), 0026 (24), 0033
  (11b), 0060 (28), 0061 (29), 0063 (31), 0064 (33);
- a bug with a flag workaround: 0006 (a speed choice over the flag; to be
  remeasured on an idle machine);
- build-time costs with a small fix: 0030 (22), 0031 (17), 0032 (11), 0034
  (20), 0035 (16), 0062 (30), 0066 (35);
- an optimization: 0007 (kept because 0009 builds on it);
- a missing feature: 0013 to 0015, and 0027 (bug 27, the same bounded-depth
  frees for a member behind `Nullable`);
- local additions, no bug: 0040, 0050.

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
  L0` natively and `L0 L1 ... L7` through lean2rr before patch 0014. With
  0014 the order is Lean's in every free that starts at a container, and
  mostly below the first cell of a free that starts at a record; a list of
  handles dropped by itself closes `L0 L7 L6 … L1` (see "Order that still
  differs" in [bug 13](13-long-list-drop.md); plan §10).
- **Drop glue that may not return.** Reussir marks drop glue `mustprogress
  nounwind willreturn`. Through lean2rr's runtime (`leanrt::drop::run`,
  and the drain hook of [0040](local-additions.md)) a free can run Lean
  continuations, which might not return (`IO.Process.exit` inside a sync
  dependent), which would falsify `willreturn`. No concrete miscompile was
  found. (Review RV8, side note on 0040.)
- **TokenReuse's locality bonus is dead code (not a bug).** A review of
  0030-0035 pointed at `lib/Transformation/TokenReuse/TokenReuse.cpp`,
  function `heuristic`: walking from a new cell's field back to the cell it
  was loaded from, it steps from a dispatch arm's argument to
  `dispatch.getValue()`, the dispatch's *result*, where the scrutinee
  (`getVariant()`) is meant; for a dispatch without a result the next step
  reads a null value. The line never runs: the field list the walk starts
  from is read from `create.getRcPtr().getDefiningOp()`, the `rc.create`
  itself (its `getValue()` was meant), so the list is always empty. (Also,
  in rrc's pipeline the first `ConvertToSTD` lowers every
  `record.dispatch` before TokenReuse runs.) So the intended bonus for
  reusing the cell a new cell's fields come from never applies (a missed
  optimization: a donor scores 2 where the code means 4, a local probe
  `tv2.mlir`), and the crash is
  latent: with only the first mistake corrected, `reussir-opt
  --reussir-token-reuse` crashes (SIGSEGV) on a result-less dispatch
  (a local probe `tv3.mlir`, checked on a throwaway build). A fix needs
  both changes
  and would change which token is reused, a performance change; not
  patched.

## Missing features that cost lean2rr performance

Not bugs, but each one costs lean2rr measurably:

- **Borrowed parameters.** Reads of arrays and strings through the runtime
  take the container owned, so each read retains and releases it.
  Traversals that keep unchanged nodes pay the same on fields (about 1.5x
  native on an `Expr.replace`-style DAG traversal).
- **A one-word `Nat`** (done locally: [0050](local-additions.md), tagged
  opaque handles; `Nat` and `Int` are one tagged word, as natively; before,
  `Nat` was a two-word `[value]` enum and `Std.TreeMap Nat Nat` used about
  1.5x native memory).
- **`[value]` types across the FFI.** Arrays of enumerations or `[value]`
  records need runtime-side representations or wrappers.
- **Guaranteed tail calls.** Mutual tail calls are sibling calls only when
  all arguments fit in registers.
