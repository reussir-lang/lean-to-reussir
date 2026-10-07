# 3. Rust allocations through Reussir's global allocator are 16-aligned

**Kind:** cost (run time), with an intended part. Not a bug: programs are
correct. Reussir's runtime raises Rust allocations to 16-byte alignment on
purpose (intended); the slow frees that this caused were avoidable (a
cost). Patches 03-a and 03-b are an optimization.

## Summary

**Kind:** cost (run time); the 16-byte alignment itself is intended.
**Status:** patched (03-a, with the review fixes in 03-b), not applied in
`./reussir` yet (made on branch `l2r-inline` of a Reussir worktree, on
36-a); reviewed (review-inline: three small findings, fixed in 03-b; a
second look is pending). lean2rr's
runtime also allocates its own objects with `mi_malloc` (below).

**Verdict: cost, with an intended part.** `crates/reussir-rt/src/alloc.rs`
forces every Rust allocation to at least 16-byte alignment through the
backend's aligned path on purpose, and `.cargo/config.toml` documents
`MI_MAX_ALIGN_SIZE=8` as deliberate. Keeping Rust's requested alignment is
not a Reussir promise: the alignment is intended. But for a size of at
most 64 bytes that is not a multiple of 16 (every larger size class is a
multiple of 16), mimalloc's aligned path sometimes allocates a larger
block and moves the pointer. That marks the block's page, and every later
free in that page takes mimalloc's slow path, also the frees of Reussir's
own objects, which share the pages. This part is avoidable: patch 03-a
rounds the size up to a multiple of 16, and mimalloc then gives the
alignment from the block's size class. In lean2rr programs the slow path
took up to 5.2% of the instructions (monadic-interp) and 4.0%
(unionfind), and it varied from run to run of one executable, with the
pages that got marked.

## Symptom and repro

Repro [`repros/bug03-global-alloc-align.rr`](repros/bug03-global-alloc-align.rr):
a Rust texture that keeps 1000 `Box<u64>` and 1000 `mi_malloc(8)` blocks
alive and counts the 16-aligned ones. Then it counts the boxes that do
not start a mimalloc block (a moved pointer): it visits the heap's blocks
with `mi_heap_visit_blocks`. (Until 2026-10-06 the repro timed
allocate/free pairs through `Box::new` and through `mi_malloc` instead:
6-33% longer through `Box::new`, on a loaded machine.)

**Command.** `rrc bug03-global-alloc-align.rr -O aggressive`.

**Expected** (the alignment kept, no moved pointer): every box
16-aligned, none moved.

**Actual on ef922049** and on `l2r-anybox` 1eb710b4:

    Box<u64> 16-aligned: 1000 of 1000; mi_malloc(8) 16-aligned: 500 of 1000
    boxes moved inside a larger block: 500 of 1000

With 03-a: FIXED, `boxes moved inside a larger block: 0 of 1000` (every box still
16-aligned).

**lean2rr.** Cachegrind (`Ir`) of monadic-interp (1000), unionfind (70000)
and liasolver (16), three runs of one executable each (lean2rr builds with
36-a, without SVE for valgrind 3.22; "slow free" is the instructions of
`mi_free_generic_local` and `_mi_page_ptr_unalign`):

| program | run | without 03-a | slow free | with 03-a | slow free |
|---|---|---|---|---|---|
| monadic-interp | 1 | 1,153,426,227 | 141 | 1,153,409,306 | 9 |
| | 2 | 1,204,395,624 | 63,054,058 (5.24%) | 1,153,409,338 | 9 |
| | 3 | 1,153,426,257 | 141 | 1,153,409,342 | 9 |
| unionfind | 1 | 371,916,474 | 14,852,475 (3.99%) | 359,970,137 | 5,437 |
| | 2 | 371,916,020 | 14,852,475 (3.99%) | 359,969,592 | 5,437 |
| | 3 | 359,941,950 | 5,727 | 359,969,596 | 5,437 |
| liasolver | 1 | 235,157,851 | 3,978 | 235,144,457 | 489 |
| | 2 | 235,156,437 | 4,040 | 235,143,948 | 489 |
| | 3 | 235,155,955 | 3,978 | 235,144,461 | 489 |

Without 03-a, a run of monadic-interp took 4.4% more instructions than
the other two, and two runs of unionfind 3.3% more than the third, all
in the slow free path. With 03-a the three runs of each program agree to
within 600 instructions, and the slow free path is gone (what is left
are frees of other kinds). Against the best run without 03-a the counts
change by -0.001% (monadic-interp), +0.008% (unionfind) and -0.005%
(liasolver): the rounding itself costs nothing measurable. (The
runtime's own profiles saw up to 8.0% for monadic-interp, 5.5% for
unionfind and 2.5% for liasolver; these three runs of liasolver happened
to mark no page.)

## Cause

`crates/reussir-rt/src/alloc.rs`: `ReussirGlobalAlloc` raises every request
to `GLOBAL_MAX_ALIGN = 16` (`max_align_t`, on purpose: other code sharing
the heap may assume it). Reussir builds mimalloc with
`MI_MAX_ALIGN_SIZE=8`, so every Rust `Box`/`Vec` allocation goes to
`mi_malloc_aligned`. Checked in the mimalloc Reussir pins
(`libmimalloc-sys` 0.1.44, its default v2 sources, `alloc-aligned.c`):

- `mi_heap_malloc_zero_aligned_at` first takes the next free block of the
  size's class if the alignment is at most the size and the block happens
  to be 16-aligned.
- Otherwise `mi_heap_malloc_zero_aligned_at_generic` takes a plain block
  only if `mi_malloc_is_naturally_aligned` holds: the alignment is at most
  the size, and the class's block size is a multiple of 16 (and at most
  64 KiB). For 24 bytes (class 24) it does not hold, nor for any size
  below 16.
- Then `mi_heap_malloc_zero_aligned_at_overalloc` allocates `size + 15`
  bytes and, if that block is not 16-aligned, moves the pointer and marks
  the page (`mi_page_set_has_aligned(page, true)`).

`mi_free` takes the generic path for a page with that mark
(`page->flags.full_aligned != 0` in `free.c`): `mi_free_generic_local`,
which finds the block start with `_mi_page_ptr_unalign`. The mark stays
while the page lives, and the page holds other objects of the same size
class too.

## lean2rr

The runtime (`runtime/leanrt/src/alloc.rs`) allocates its own objects
(strings, arrays, big numbers) with `mi_malloc`/`mi_realloc` directly.
This stays with 03-a: these objects need only 8-byte alignment, and their
blocks stay smaller.

## Patch

Patch files
[`patches/03-a-global-alloc-size-classes.patch`](patches/03-a-global-alloc-size-classes.patch)
(commit `ad079b37` on branch `l2r-inline` of a Reussir worktree, made on
36-a) and
[`patches/03-b-round-only-mimalloc.patch`](patches/03-b-round-only-mimalloc.patch)
(commit `136d9a9f`, after 36-b: the review's fixes). Both change only
`crates/reussir-rt/src/alloc.rs`.

Under the mimalloc backend, `ReussirGlobalAlloc::alloc` and `realloc` ask
the backend for the size rounded up to a multiple of 16 (`global_size`),
with the same alignment (at least 16). `dealloc` is unchanged; the
default `alloc_zeroed` calls `alloc`. The language heap (`__reussir_*`)
keeps its 8-byte size classes. The libc fallback (the sanitizer runtime
variants, miri) gets the size as asked (03-b): `malloc` gives 16-byte
alignment anyway, and the exact size lets the sanitizers see a Rust-side
overflow past the end of a block.

**Why it gives the alignment without moving a pointer** (mimalloc v2 as
pinned, checked in its sources):

- Every size class of a multiple of 16 bytes is a multiple of 16: the
  classes up to 64 bytes are exact (8, 16, 24, ... with
  `MI_MAX_ALIGN_SIZE=8`), and the larger ones are even numbers of words
  (`MI_PAGE_QUEUES_EMPTY` in `init.c`: 80, 96, 112, 128, 160, ...).
- A page starts at a 64 KiB slice boundary plus an offset
  (`_mi_segment_page_start_from_slice` in `segment.c`). For blocks up to
  64 KiB the offset is made of the block size (`3 * block_size` or
  `block_size`) and of `block_size - pstart % block_size` (taken when the
  page has room for it; it makes the start a multiple of the block size),
  so it is a multiple of 16 when the block size is: every block of the
  page is 16-aligned. A larger block is alone in its page, at offset 0.
- So `mi_malloc_aligned(size, 16)` either takes the class's free block
  (always 16-aligned) or finds the size naturally aligned and takes a
  plain block. Above 64 KiB it allocates `size + 15` bytes, but that
  block is 16-aligned, so it moves nothing and marks nothing.
  `mi_realloc_aligned` keeps a block that fits and is aligned, or
  allocates as above and copies.

The cost of the rounding: a Rust allocation of 8, 24, 40 or 56 bytes
takes 16, 32, 48 or 64 bytes (mimalloc's default build, with
`MI_MAX_ALIGN_SIZE=16`, does the same); requests over 64 bytes keep their
size class. Building mimalloc with `MI_MAX_ALIGN_SIZE=16` would also
remove the moves, but it would give every Reussir object 16-byte classes:
a 24-byte box would take 32 bytes, the loss that `.cargo/config.toml`'s
value 8 avoids. Under the `mimalloc-v3` feature (not the default), with
`MI_MAX_ALIGN_SIZE=8`, `sizeof(mi_page_t)` is 120 bytes, so most pages of
classes that are not powers of two start 8 bytes off 16, and v3's natural
alignment check accepts only power-of-two classes: most blocks still move
there (the review saw 9,519 of 10,614). The alignment is right with
either version; the whole-block test runs only with v2.

**Why it is correct.** Rust's `GlobalAlloc` contract allows a larger
block than asked: `dealloc` and `realloc` get the asked size back, and
the backends ignore it (they find the block from the pointer). A
`Layout`'s size is at most `isize::MAX`, so the rounding does not
overflow. The alignment passed to the backend is unchanged.

**Verification.**

- Unit tests (new, `alloc.rs`; `cargo test -p reussir-rt --release --lib
  alloc::` with the repository's `.cargo/config.toml`, so mimalloc is
  built with `MI_MAX_ALIGN_SIZE=8`): `global_alloc_is_16_aligned`
  (`alloc`, `alloc_zeroed` and `realloc` up and down, sizes 1 to 144 and
  255 to 16 MiB + 8, alignments 1 to 16: every pointer 16-aligned, zeroed
  memory zero, contents kept) and `global_alloc_takes_whole_blocks` (under
  mimalloc v2, 4 x 1027 live allocations: each `mi_usable_size` is the
  class size of its rounded size, so no pointer was moved). Both pass, and
  so do the four old allocator tests. Without the rounding,
  `global_alloc_takes_whole_blocks` fails (at size 1). After 03-b, the
  tests pass with the default features (6 tests), with
  `--no-default-features` (the libc fallback, 5) and with
  `--no-default-features --features mimalloc-v3` (5).
- `run.sh bug03`: FIXED (above).
- lean2rr (deptypes 91fe1e3) on `l2r-inline` ad079b37 (36-a and 03-a):
  `tests/runtime/ffi-inline-check.sh` passes; the 18 classic programs
  pass `tests/oracle.py check --sizes small`; the lean2rr counts above.
  Reussir's lit tests `frontend/ffi_*`, `frontend/str_ffi*`,
  `frontend/polyffi*`, `llvmpass/*` and `conversion/trampoline*` (40
  tests) pass. On 136d9a9f (with 36-b and 03-b): the same lit tests and
  the new one (41), `ffi-inline-check.sh`, `run.sh bug03` (FIXED).
- qsort (issue 36's entry): the unpatched program runs in one of two
  page-retire states from run to run; with 03-a every run takes the
  second one. In the second state mimalloc's `_mi_page_retire` costs more
  in the array growth (684,411 instead of 368,311 instructions at size
  80, about 0.3% of the program); against an unpatched run in the same
  state, 03-a changes nothing there.

**Review.** Round review-inline (local notes `review-inline/`; the
coordinator judged the findings):

- F5 (low): the rounding also applied to the libc fallback, where it hid
  Rust-side overflows of up to 15 bytes from the sanitizers. Fixed in
  03-b (rounding only under `all(feature = "mimalloc", not(miri))`).
- F6 (low): under `--features mimalloc-v3` the whole-block test failed (at
  size 33). Fixed in 03-b (the test is for v2); the v3 note above is
  corrected.
- F7 (documentation): "a page's blocks start at a multiple of the block
  size" was not always true (the conclusion holds: 64 KiB slices, offsets
  that are multiples of 16), and the moves happen only for sizes of at
  most 64 bytes. Corrected above and in `alloc.rs`.

A second look at 03-b is pending.

## Upstream note

A global allocator that promises `max_align_t` on top of a heap built for
8-byte alignment can round each size up to a multiple of 16, as 03-a
does: the size class then gives the alignment.
