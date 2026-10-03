# The local Reussir patches, in detail

These files explain each of lean2rr's local Reussir patches in depth: what
went wrong, where in Reussir, why, what the patch changes and how it was
checked. They expand on `../../docs/reussir-bugs.md` (one section per bug)
and `../README.md` (how to apply the patches). The patches are against
Reussir `ef922049`. In `./reussir` they are the ten commits of the local
branch `l2r-local`.

## Policy

Reussir is patched only when a bug breaks lean2rr's output (a crash of rrc
or of the program, wrong results, or a serious slowdown) and lean2rr has no
reasonable workaround. Otherwise lean2rr works around the bug, and the bug
is still documented in `docs/reussir-bugs.md`. The patches are local only.
They are never pushed or submitted upstream; the "Upstream note" at the end
of each file is only text someone could use later. Each patch passed
adversarial review before it was applied: code review, differential
fuzzing against an independent reference evaluator, ASan builds, and
lean2rr's runtime suite and corpus. The first eight patches went through
three rounds. 0014 went through a fourth round and was revised twice
(rounds 4, 4b, 4c). 0015 went through a fifth.

## What each patch really fixes (audit, 2026-10-02)

An independent audit checked every entry of `docs/reussir-bugs.md` against
Reussir's own documentation, tests and source (verdicts at the start of
each section there). For the patches:
- 0002, 0004, 0005, 0009 (bugs 9 and 14) and 0012 fix real bugs (0012's is
  in Reussir's parser dependency `cstree`).
- 0006 fixes a real bug, but lean2rr could avoid it with
  `--nullary-variant-encoding arch-independent` (or `boxed`): the patch is
  a speed choice over that flag (indicative measurements in bug 6's
  section; to be remeasured on an idle machine).
- 0007 is an optimization, not a bug fix: the output was correct, and
  lean2rr's `lazy-fields` pass already avoids the slow shapes. It stays
  because 0009 uses the helper it adds; if it brings lean2rr nothing with
  `lazy-fields` on, 0009 should be rebased without it and 0007 dropped.
- 0013, 0014 and 0015 implement a missing feature (bounded-depth frees,
  Lean's release order) rather than fix a bug: Reussir's drop glue recurses
  by design, as Rust's does. lean2rr needs it, and its runtime needs 0014.

## Patches

| Patch | Bug | Problem | Fix | Read |
|---|---|---|---|---|
| `0002` | 2 (structures) | A structure built in the reused cell of another structure type of the same size skips storing a field that sits at a different offset, so the field keeps stale bytes. | Skip a field's store only when the old and new box types are identical. | [0002.md](0002.md) |
| `0004` | 4 | Copy avoidance compares two structurally equal recursive record types forever: rrc dies with SIGSEGV. | Compare coinductively (a pair already under comparison counts as equal), and also compare capability and `fixed`. | [0004.md](0004.md) |
| `0005` | 5 | TokenReuse frees a token on the missing else path of a one-armed `scf.if` through a dangling block: rrc SIGSEGV. | Create the else block (a bare `scf.yield`) and put the free there. | [0005.md](0005.md) |
| `0006` | 6 | On aarch64 (TBI encoding), the static dummy cell behind a nullary constructor is freed once its 32-bit count wraps after 2^32 references. | The decrement's "last reference" branch checks for the type's immediates and frees nothing for one. | [0006.md](0006.md) |
| `0007` | 7 | Token reuse picks member decrements that can never free over the matched cell, so a BST insert that returns the node for an equal key reallocates every node of the path (about 6x slower). | Sink the arm's retains into the branch that releases the scrutinee, so that path gets a destructuring decrement. | [0007.md](0007.md) |
| `0009` | 9 and 14 | `fuseArm` replaces retains that the release cannot replace (a member retained twice, or consumed before the release): use after free. | Fuse at most one retain per member, and none when a bound member is consumed before the release. | [0009.md](0009.md) |
| `0012` | 12 | cstree's node cache swaps a syntax subtree for an earlier one with the same 32-bit hash: bogus errors, or a silently different program on large files. | Build syntax nodes without the node cache. Tokens are still cached. | [0012.md](0012.md) |
| `0013` | 13 | Drop glue frees a cell only after the recursive release of its tail returns: one stack frame per list cell, so the stack overflows. | Inside drop glue, release through a new `drop_and_free`, which frees the cell first and releases the chain member by a tail call (a loop). | [0013.md](0013.md) |
| `0014` | 13 (13b) | With 0013, a value deep along a member that the loop does not follow (a left-deep tree with fresh right children, a rose tree) still recurses once per level. | A per-thread stack of pending releases, like Lean's `lean_del`, linked through the deferred cells' own headers. Glue defers members and `drop_in_place` drains. | [0014.md](0014.md) |
| `0015` | 13 (13b, runtime) | 0014's runtime bookkeeping costs allocation-heavy programs about 10% (17-20% user cycles). | The same stack, behaviour and order, with a cheaper implementation: one thread-local with no destructor and fast paths. | [0015.md](0015.md) |
| `0016` | 21 | An unterminated `[:` in a texture's Rust body (no `:]` after it) is dropped before rustc sees it, so a Lean string literal containing `[:` printed without it. | Write the pending `[:` before the rest of the body, as Reussir's Rust implementation of the substitution does. | [0016.md](0016.md) |
| `0017` | 23 | The compiled texture modules are linked with one `Linker::linkModules` call each; every call's linker walks the whole module linked so far, so the link is quadratic in the number of instances (65 minutes for a Std.Http program with 8241). | One `llvm::Linker` for the whole gather, `linkInModule` per module, as `llvm-link` does (6.4 s). | [0017.md](0017.md) |
| `0050` | (feature) | A small `Nat` is not a pointer, but Reussir increments every opaque handle at its address and calls its drop hook: a one-word `Nat` (a tagged scalar or a pointer to a big number, as natively) was impossible, and `Nat` took 16 bytes. | `#[ffi(rust = "...", tagged)]`: the type carries a `tagged` flag, and `rc.inc`/`rc.dec` of such a handle touch the count or call the hook only when the low bit is clear. | [0050.md](0050.md) |

Dependencies: the patches apply on ef922049 in the order 0006, 0004, 0002,
0007, 0009, 0005, 0013, 0012, 0014, 0015 (`../README.md`). Some of that
order is required:
- 0009 uses `consumesFusedMember`, which 0007 adds.
- 0014 rewrites 0013's code, and 0015 rewrites 0014's runtime.
- 0012 also applies alone.
- lean2rr's runtime needs 0014 to build, because `leanrt::drop` uses
  `reussir_rt::drop`.

## Reussir bugs that are not patched

| Bug | Problem | Why not patched | Section |
|---|---|---|---|
| 1 | A `[value]` enum is moved as the LLVM struct of one "representative" arm, so another arm's bytes on its padding or on an `i1` field are lost. | lean2rr emits only unaffected `[value]` enums: enumerations without fields (`Nat`/`Int` are tagged handles, 0050). Other multi-arm types are shared enums. | [bug 1](../../docs/reussir-bugs.md#1-value-enum-payloads-lost-in-the-llvm-lowering) |
| 2 (variants) | In-place reuse of a variant cell skips a field's store when the default packed layout puts the field at another offset in the new arm. | lean2rr passes `--no-pack-record-members` and orders fields by decreasing alignment, so equal member types at indices 0..i give equal offsets. | [bug 2](../../docs/reussir-bugs.md#2-in-place-reuse-skips-stores-of-fields-that-sit-elsewhere-in-the-new-record) |
| 3 | Reussir's global allocator raises every Rust allocation to 16-byte alignment, which sends it to mimalloc's aligned (slower) path. | Speed only. lean2rr's runtime allocates its own objects with `mi_malloc`/`mi_realloc` directly. | [bug 3](../../docs/reussir-bugs.md#3-rust-allocations-through-reussirs-global-allocator-are-16-aligned) |
| 8 | Under `--no-pack-record-members`, a padding "lift" gives LLVM a larger layout than the one Reussir allocates (heap overflow). | lean2rr never emits the shape: its records have no padding between members, and its `[value]` structs have a single field whose size is a power of two. | [bug 8](../../docs/reussir-bugs.md#8-a-padding-lift-breaks-declaration-order-layouts) |
| 10 | Closure devirtualization prints closure result types exponentially (build time and memory). | The driver passes `--no-closure-wpd`. It costs nothing measurable, since lean2rr dispatches its function values itself. | [bug 10](../../docs/reussir-bugs.md#10-closure-devirtualization-prints-result-types-exponentially) |
| 11 | MLIR's interprocedural SCCP is superlinear on large call graphs (build time). | Build time only, and the cause is in MLIR's data-flow solver. The programs it was blamed for were mostly bug 20, and they build in acceptable time once bug 20 is worked around. lean2rr has no workaround of its own. | [bug 11](../../docs/reussir-bugs.md#11-interprocedural-sccp-is-superlinear-on-large-call-graphs) |
| 15 | A `match` on a `Nullable` whose arms yield a counted value does not compile. | lean2rr does not use `Nullable`. | [bug 15](../../docs/reussir-bugs.md#15-a-match-on-a-nullable-whose-arms-yield-a-counted-value-does-not-compile) |
| 16 | With `--reuse-across-call`, the generated code grows quadratically with match nesting depth (build time and memory). | lean2rr cuts deep tail paths and deep `let` values into separate functions (`LeanToReussir/Outline.lean`). | [bug 16](../../docs/reussir-bugs.md#16-reuse-across-calls-is-superlinear-in-the-nesting-depth-of-matches) |
| 17 | rrc memory is quadratic in the length of a straight-line function on `Nat` (build time). | The same outlining, into parts of at most 64 `let`s on a path. `Array Nat` literals become tables. | [bug 17](../../docs/reussir-bugs.md#17-rrc-memory-is-quadratic-in-the-length-of-a-straight-line-function-on-nat) |
| 18 | Building only the `rrc` target does not link (a missing CMake dependency). | It affects only Reussir's own build: build the default target. | [bug 18](../../docs/reussir-bugs.md#18-the-rrc-build-target-alone-does-not-link) |
| 19 | A `Cell` of a `[value]` record with counted members does not compile (a `field` reference is passed where the outlined glue expects an unspecified one). | `[value]` records in references are boxed (`ElemBox`); `Nat`/`Int` are counted handles (0050), which cells hold directly. | [bug 19](../../docs/reussir-bugs.md#19-a-cell-of-a-value-record-with-counted-members-does-not-compile) |
| 20 | The MLIR inliner grows lean2rr's conversion code exponentially (build time and memory). | lean2rr marks its conversion, unboxing and uniform-code application functions `#[transform_anchor]`, which keeps them out of that inliner. | [bug 20](../../docs/reussir-bugs.md#20-the-mlir-inliner-grows-lean2rrs-conversion-code-exponentially) |

## Terms used in these files

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

## State of the patched build

`docs/reussir-bugs/run.sh` on the current `./reussir` build (ef922049 + the
ten patches), run on 2026-10-02 from a copy of the script under `/tmp`:

    bug 02a  FIXED       prints 7005009   [-O aggressive --no-pack-record-members]
    bug 02b  REPRODUCES  prints 11001, expected 5001   [-O aggressive]
    bug 04   FIXED       compiles, prints 1005   [-O aggressive]
    bug 05   FIXED       compiles, prints 3   [-O aggressive]
    bug 06   FIXED       N = 4294967300: prints 4294967300   [lean2rr's flags]
    bug 07   FIXED       insert returning t is 1.04x the rebuilding insert   [lean2rr's flags]
    bug 09   FIXED       prints 0 (no wrong result in 1000 runs)   [lean2rr's flags]
    bug 12   FIXED       prints 424242   [-O aggressive]
    bug 13   FIXED       list, 1M cells, 8 MB stack: prints 1000000   [lean2rr's flags]
    bug 13   FIXED       snoc, 1M cells, 8 MB stack: prints 1000000   [lean2rr's flags]
    bug 13   FIXED       lspine, 1M cells, 8 MB stack: prints 1000000   [lean2rr's flags]
    bug 14   FIXED       prints 0 (no wrong result in 1000 runs)   [lean2rr's flags]

("lean2rr's flags" are `-O aggressive --no-pack-record-members
--reuse-across-call`.) `02b` is the variant half of bug 2, which is not
patched. The Lean half of the bug 13 repro needs a lean2rr build, which the
`/tmp` copy did not have. `docs/reussir-bugs.md` reports it FIXED from 0013
(extended) onwards.

The unpatched lines quoted in each file come from a recorded run of the
same script on unpatched ef922049. The review notes cited as "round N,
finding X" are in `~/Documents/l2r-scratch/rv-patches/` (`FINDINGS.txt`
for round 1, `roundN/FINDINGS.txt` after that). They are scratch files
outside this repository.
