# Reussir bugs met by lean2rr

Every Reussir problem lean2rr has run into, including those it works around
or never triggers. Each entry has one file, `NN-*.md`, with a repro, the
cause in Reussir's source where known, what lean2rr does about it, and, if
it is patched, the local patch explained hunk by hunk. Most entries are
bugs; the audit below found a few that are intended behaviour, a missed
optimization, a missing feature, or build costs of a stock pass or an
opt-in flag (column *Kind*).

Reussir revision: `ef922049`. The checkout at `./reussir` is not part of
this repository.

- `NN-*.md`: one file per entry (status table below).
- [`patches/`](patches/): the local patches (`git format-patch` output
  against ef922049); [applying them](#applying-the-patches).
- [`repros/`](repros/): the repro programs and `run.sh`, which builds and
  runs them; [running them](#running-the-repros).

## Policy

- Every Reussir problem lean2rr meets is documented here, with a repro.
- A real Reussir bug (verified reproducible erroneous behaviour) gets a
  small local patch, reviewed adversarially before it is applied, even if
  lean2rr never triggers it or works around it.
- Entries that are intended behaviour, costs of a stock pass or an opt-in
  flag, missed optimizations, or unclear stay unpatched, with the reason in
  their file. Patches 0007 (bug 7, an optimization that 0009 builds on)
  and 0013 to 0015 (bug 13, a missing feature lean2rr's runtime needs)
  predate this rule and stay, for the reasons in their files.
- Patches are local only: never pushed or submitted upstream. The
  "Upstream note" at the end of a patched entry is only text someone could
  use later.
- lean2rr's workarounds stay, so that lean2rr also works with an unpatched
  Reussir. The exception is bug 13: lean2rr's runtime needs 0014 to build.

## Status

Column *Patch*: "none yet" marks a bug whose patch is not written yet;
"none" an entry that stays unpatched (the reason is in its file). Column
*Applied*: whether the patch is on `./reussir`'s branch `l2r-local`, that
is, in the [apply list](#applying-the-patches).

| # | Kind | Effect | Affects lean2rr output? | lean2rr workaround | Patch | Review | Applied |
|---|---|---|---|---|---|---|---|
| [1](01-value-enum-payload.md) | bug | `[value]` enum payload bytes lost when a variant is moved | no, shape avoided | emits only unaffected `[value]` enums | none yet | - | - |
| [2](02-reuse-field-store.md) | bug | in-place reuse skips the store of a field that sits elsewhere in the new cell | structures: yes, wrong values; variants: no | variants: `--no-pack-record-members` and fields ordered by alignment; structures: none | 0002 (structures); variants: none yet | 0002 passed | 0002 yes |
| [3](03-global-alloc-align.md) | intended | Rust allocations take mimalloc's aligned path | speed only | runtime calls `mi_malloc` itself | none | - | - |
| [4](04-recursive-type-compare.md) | bug | rrc recurses forever on two equal recursive types (SIGSEGV) | yes, rrc crash | driver retries without `--reuse-across-call` | 0004 | passed | yes |
| [5](05-one-armed-if.md) | bug | TokenReuse crashes on a one-armed `if` (SIGSEGV) | yes, rrc crash | prelude panics avoid the shape; user code can still hit it | 0005 | passed | yes |
| [6](06-static-count-wrap.md) | bug, with a flag workaround | a static cell is freed after 2^32 references | yes, crash | `--nullary-variant-encoding arch-independent` or `boxed` (not used: 0006 keeps the default encoding's speed) | 0006 | passed | yes |
| [7](07-phantom-reuse-donor.md) | missed optimization | token reuse picks decrements that never free | yes, speed | fields bound lazily (plan §5.5) | 0007 | passed (revised after round 2) | yes |
| [8](08-padding-lift.md) | bug | padding "lift" gives LLVM a larger layout than Reussir's | no, shape never emitted | - | none yet | - | - |
| [9](09-duplicate-bound-member.md) | bug | a member used twice loses a reference (use after free) | yes, through Reussir's inliner | none | 0009 | passed (revised after round 2) | yes |
| [10](10-closure-type-print.md) | bug (build time) | closure devirtualization prints types exponentially | yes, build time and memory | `--no-closure-wpd` | none yet | - | - |
| [11](11-sccp-call-graph.md) | cost (stock MLIR pass) | interprocedural SCCP is superlinear (build time) | yes, build time of large programs | none (the towers it was blamed for were mostly bug 20) | none | - | - |
| [12](12-node-cache-collision.md) | bug (in cstree) | the parser swaps syntax subtrees whose hashes collide | yes, wrong code or bogus errors on very large files | none | 0012 | passed | yes |
| [13](13-long-list-drop.md) | missing feature | releasing a long list or a deep tree recurses once per cell | yes, stack overflow, 2x time and memory | none | 0013, 0014, 0015 | 0013 passed (extended after round 2); 0014 passed (round 4, revised twice); 0015 (speed of 0014's runtime) passed (round 5) | yes |
| [14](14-member-consumed-before-release.md) | bug | a member consumed before the release loses a reference (use after free) | yes, through Reussir's inliner | none | in 0009 | passed | yes |
| [15](15-nullable-match-yield.md) | bug | a `match` on a `Nullable` yielding a counted value does not compile | no, `Nullable` not used | - | none yet | - | - |
| [16](16-nested-io-matches.md) | cost (opt-in flag) | reuse across calls is superlinear in match nesting (build time) | yes, build time and memory | deep tail paths and `let` values outlined, recursive functions included | none | - | - |
| [17](17-long-nat-block.md) | unclear | rrc memory is quadratic in a straight-line `Nat` function (build time) | yes, build memory | long tail paths and `let` values outlined, recursive functions included; `Array Nat` literals as tables | none | - | - |
| [18](18-rrc-target-deps.md) | bug (build system) | the `rrc` build target alone does not link | no, Reussir's build only | build the default target | none yet | - | - |
| [19](19-cell-of-value-record.md) | bug | a `Cell` of a `[value]` record with counted members does not compile | yes, compile error | `Nat`/`Int` references in two cells; other `[value]` records boxed | none yet | - | - |
| [20](20-statet-tower.md) | unclear | the MLIR inliner grows lean2rr's conversion code exponentially (build time) | yes, build time and memory (monad transformer towers did not build) | conversion, unboxing and uniform-code application functions marked `#[transform_anchor]` | none | - | - |
| [21](21-unterminated-placeholder.md) | bug | an unterminated `[:` in a polymorphic FFI texture is dropped | yes, wrong output (a string literal containing `[:` printed without it) | `[` escaped (`\x5b`) in the string literal table | 0016 | checked by the round-6 review (RV6L-01) | no |
| [22](22-wildcard-wide-enum.md) | cost | a wildcard arm over a wide enum costs N^3 code (copied per constructor, releases expanded in line in each copy) | yes, build time (a derived BEq on 40 constructors: 9 minutes) | held wide values released out of line in wildcard arms (`l2r_sink`) | none | - | - |
| [23](23-polyffi-link.md) | bug (build time) | the compiled polymorphic-FFI modules are linked one call each, quadratic in their number | yes, build time (a Std.Http program with 8241 instances: 65 minutes of linking) | none | 0017 | under review | no |

Status words used in the entries' summaries:

- *worked around*: lean2rr avoids the construct or works around it.
- *patched*: a local patch fixes it (whether it is applied: column
  *Applied* above).
- *does not affect lean2rr*: lean2rr never produces the triggering shape.
- *open*: lean2rr can hit it and has no fix or workaround.

## Applying the patches

`./reussir`'s local branch `l2r-local` (never pushed) is ef922049 plus ten
patches, as local commits, applied in the order of the `for` list below
(the apply list). To recreate it, from the repository root:

```sh
git -C reussir checkout -b l2r-local ef922049
for p in 0006 0004 0002 0007 0009 0005 0013 0012 0014 0015; do
    git -C reussir am "$PWD/reussir-bugs/patches/$p-"*.patch || break
done
cmake --build reussir/build
```

`git am` records them as local commits; `git apply` works as well, if you
would rather keep them as uncommitted changes. Applied this way on
2026-10-02 (to a scratch clone), the list gives exactly the tree of
`./reussir`'s `l2r-local`. The `From <sha>` line of each patch file names
the commit in the scratch checkout where it was made; `l2r-local`'s commits
have the same contents and messages (their hashes are in each entry's
*Patch* section).

Order and dependencies:

- 0009 needs 0007: it calls `consumesFusedMember`, which 0007 adds.
- 0014 rewrites 0013's code, and 0015 rewrites 0014's runtime: 0013, 0014,
  0015 in that order.
- 0012 also applies alone.
- Patches in `patches/` that are not on the list are not applied yet
  (column *Applied*). Each applies on top of the list: 0017 was made on
  top of 0016 and also applies without it.
- lean2rr's runtime needs 0014 to build (`leanrt::drop` uses
  `reussir_rt::drop`, the pending stack 0014 adds to Reussir's runtime).
  Without the others, lean2rr programs still compile, but the bugs can
  appear.

**Adding a patch:** put the file in `patches/`, write the *Patch* and
*Upstream note* sections of the entry's file, update the entry's row in the
status table, and, once it is applied to `l2r-local`, add it to the apply
list.

## Running the repros

[`repros/`](repros/) has one repro per entry: a plain Reussir program
(`bugNN-name.rr`), a Lean program built through lean2rr (`bugNN-name.lean`)
where the bug needs lean2rr's output, a small generator (`bugNN-name.py`)
where the program must be large, or a check script (bug 18). Each file
starts with what it shows, the expected output and what Reussir ef922049
does.

    reussir-bugs/repros/run.sh RRC_CHECKOUT [BUG...]

builds each repro with `RRC_CHECKOUT/build/bin/rrc`, runs it and prints one
line per repro: `REPRODUCES` (the documented bad behaviour), `FIXED` (the
expected output), `OTHER` (something else), or `SKIPPED` (a tool is
missing, or a slow repro under `QUICK=1`), with what it saw and, in
brackets, the rrc flags. BUG is a number (`1`, `02`, `13`, ...); the
default is every entry except 22, whose generator is run by hand. The
script's header documents its environment (`WORK`, a scratch directory;
`RUSTC`; `QUICK=1`, which skips the slow repros 6, 10, 11, 16, 17, 20 and
23). The Lean repros (13 and 20, and the programs generated for 16 and 17)
need Lean 4.33 and a lean2rr build (`lake build` in `lean2rr/`). The
build-time repros (10, 11, 16, 17, 20, 23) take one to three minutes each,
and 16 and 20 need 1.2 to 3 GB; bug 6 runs for about 15 s.

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
- "the ten-patch set": the nine-patch set + 0015.
- `l2r-local` + 0016, a scratch build (bug 23's measurements).

The unpatched `run.sh` lines quoted in the entries come from a recorded run
of the same script on unpatched ef922049.

### Latest recorded run

On the current `./reussir` (`l2r-local`, the apply list), 2026-10-02, with
a lean2rr build, from a scratch directory: `QUICK=1 run.sh ./reussir`, then
`run.sh ./reussir 06`. The slow repros 10, 11, 16, 17, 20 and 23 were not
run; their entries are unpatched on this build.

    bug 01   REPRODUCES  prints 0, expected 42   [-O default]
    bug 02a  FIXED       prints 7005009   [-O aggressive --no-pack-record-members]
    bug 02b  REPRODUCES  prints 11001, expected 5001   [-O aggressive]
    bug 03   REPRODUCES  Box<u64> 16-aligned: 1000 of 1000; mi_malloc(8) 16-aligned: 500 of 1000 alloc/free pairs: Box::new 0.147 s, mi_malloc 0.133 s, ratio 1.10   [-O aggressive]
    bug 04   FIXED       compiles, prints 1005   [-O aggressive]
    bug 05   FIXED       compiles, prints 3   [-O aggressive]
    bug 06   FIXED       N = 4294967300: prints 4294967300   [lean2rr's flags]
    bug 07   FIXED       insert returning t is 1.14x the rebuilding insert   [lean2rr's flags]
    bug 08   REPRODUCES  SIGSEGV (cells overflowed), expected 2550200000   [-O aggressive --no-pack-record-members]
    bug 09   FIXED       prints 0 (no wrong result in 1000 runs)   [lean2rr's flags]
    bug 12   FIXED       prints 424242   [-O aggressive]
    bug 13   FIXED       list, 1M cells, 8 MB stack: prints 1000000   [lean2rr's flags]
    bug 13   FIXED       snoc, 1M cells, 8 MB stack: prints 1000000   [lean2rr's flags]
    bug 13   FIXED       lspine, 1M cells, 8 MB stack: prints 1000000   [lean2rr's flags]
    bug 13   FIXED       lean2rr List.replicate, 40M cells, 1 GiB stack: prints (some 7)   [l2r.py]
    bug 13   FIXED       lean2rr snoc, 40M cells, 1 GiB stack: prints 0   [l2r.py]
    bug 14   FIXED       prints 0 (no wrong result in 1000 runs)   [lean2rr's flags]
    bug 15   REPRODUCES  rrc error: parent operation expected a value, but nothing is yielded   [-O aggressive]
    bug 18   REPRODUCES  rrc-build does not depend on libMLIRReussirInstrumentNonlinearFFI.a, which build.rs links
    bug 19   REPRODUCES  rrc error: operand type mismatch   [-O aggressive]
    bug 21   REPRODUCES  prints 2, expected 4   [-O aggressive]

(`run.sh` prints lean2rr's flags in full; they are abbreviated here.) Every
applied patch shows FIXED. The lines that show REPRODUCES are entries
without an applied patch on that day (status table); `02b` is the variant
half of bug 2.

## Review

Each applied patch passed adversarial review before it was applied, in
rounds repeated until one found nothing: code review, differential fuzzing
against an independent reference evaluator, ASan builds (Miri for the
runtime patches), and lean2rr's runtime suite and corpus. The patches of
the eight-patch set were reviewed in rounds 1 to 3 (one to three rounds
each). 0014 went through a fourth round and was revised twice (rounds 4,
4b, 4c). 0015 went through a fifth. The
round-6 review of lean2rr checked 0016; 0017 is under review. The review
notes cited as "round N, finding X" are scratch files outside this
repository, in `~/Documents/l2r-scratch/`: `rv-patches/FINDINGS.txt` for
round 1, `rv-patches/roundN/FINDINGS.txt` for rounds 2 to 4c,
`perf0014-review/` for round 5 and `rv6/` for round 6.

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
- *cost*: build time or memory of a stock pass or an opt-in flag, not a
  defect;
- *unclear*: a real slowdown whose cause is not shown.

Each entry's summary starts with its kind, and with the audit's verdict
where it gave one. Of the patches, by their entries' kinds,
0002, 0004, 0005, 0009 (bugs 9 and 14), 0012 (a bug in Reussir's parser
dependency `cstree`), 0016 and 0017 fix bugs; 0006 fixes a bug that has a
flag workaround (it is a speed choice over the flag; to be remeasured on an
idle machine); 0007 is an optimization (kept because 0009 builds on it);
0013 to 0015 implement a missing feature.

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

## Missing features that cost lean2rr performance

Not bugs, but each one costs lean2rr measurably:

- **Borrowed parameters.** Reads of arrays and strings through the runtime
  take the container owned, so each read retains and releases it.
  Traversals that keep unchanged nodes pay the same on fields (about 1.5x
  native on an `Expr.replace`-style DAG traversal).
- **A one-word `Nat`.** `Nat` is a two-word `[value]` enum (small or big).
  Natively it is one tagged word, so nodes with `Nat` fields are larger
  (`Std.TreeMap Nat Nat` uses about 1.5x native memory).
- **`[value]` types across the FFI.** Arrays of `Nat`, `Int` or enumerations
  need runtime-side representations or wrappers.
- **Guaranteed tail calls.** Mutual tail calls are sibling calls only when
  all arguments fit in registers.
