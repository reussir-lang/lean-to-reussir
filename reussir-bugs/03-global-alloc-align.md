# 3. Rust allocations through Reussir's global allocator are 16-aligned

## Summary

**Kind:** intended behaviour. **Status:** worked around (in the runtime).
No patch.

**Verdict: intended behaviour.** `crates/reussir-rt/src/alloc.rs` forces
every Rust allocation to at least 16-byte alignment through the backend's
aligned path on purpose, and `.cargo/config.toml` documents
`MI_MAX_ALIGN_SIZE=8` as deliberate. Keeping Rust's requested alignment is
not a Reussir promise; lean2rr's runtime calling `mi_malloc` itself is the
right answer, not a workaround.

Reussir's global allocator raises every Rust allocation to 16-byte
alignment, which sends it to mimalloc's aligned (slower) path. Speed only.

## Symptom and repro

Repro [`repros/bug03-global-alloc-align.rr`](repros/bug03-global-alloc-align.rr):
a Rust texture that keeps 1000 `Box<u64>` and 1000 `mi_malloc(8)` blocks
alive and counts the 16-aligned ones, then times allocate/free pairs of 16
bytes through `Box::new` and through `mi_malloc` (best of 5 rounds of 20
million).

**Command.** `rrc bug03-global-alloc-align.rr -O aggressive`.

**Expected** (an allocator that keeps Rust's requested alignment): about
half of the boxes 16-aligned, like the `mi_malloc(8)` blocks.

**Actual on ef922049.**

    Box<u64> 16-aligned: 1000 of 1000; mi_malloc(8) 16-aligned: 500 of 1000
    alloc/free pairs: Box::new 0.179 s, mi_malloc 0.145 s, ratio 1.24

The pairs took 6-33% longer through `Box::new` over five runs on the
loaded test machine; allocating batches of 1000 and then freeing them
showed no clear difference.

## Cause

`crates/reussir-rt/src/alloc.rs`: `ReussirGlobalAlloc` raises every request
to `GLOBAL_MAX_ALIGN = 16` (`max_align_t`, on purpose: other code sharing
the heap may assume it). Reussir builds mimalloc with
`MI_MAX_ALIGN_SIZE=8`, so every Rust `Box`/`Vec` allocation goes to
`mi_malloc_aligned`, and later frees in pages holding aligned blocks take
mimalloc's generic path. Checked in the mimalloc Reussir pins
(`libmimalloc-sys` 0.1.44, its default v2 sources): an aligned allocation
that had to be shifted marks its page (`mi_page_set_has_aligned(page,
true)` in `alloc-aligned.c`), and `mi_free` takes the generic path for
such a page (`page->flags.full_aligned != 0` in `free.c`).

## lean2rr

The runtime (`runtime/leanrt/src/alloc.rs`) allocates its own objects
(strings, arrays, big numbers) with `mi_malloc`/`mi_realloc` directly.
