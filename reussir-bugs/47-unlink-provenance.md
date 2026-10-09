# 47. The pending stack rebuilds a linked cell's pointer with another cell's provenance

## Summary

**Kind:** bug (latent UB; no miscompile seen). **Status:** fixed in our
patch 13-c (folded in on 2026-10-09). The faulty code is lean2rr's own:
13-c wrote today's `link` and `unlink`, and 13-c was never offered
upstream, so the fix went into 13-c, not into a new patch. The series
keeps its 35 files; 13-c's file has the fix and a test, and 40-a's file
was made again for its moved context. The rebuilt stack is branch
`l2r-base2` (head `b2e4a47e`) of the Reussir checkout since 2026-10-09; the stack before the fold (`71f17ae2`) stays
reachable. No wrong result was known before the fix.

**Verdict: bug.** Before the fix, the pending stack of Reussir's runtime
(`crates/reussir-rt/src/drop.rs`) broke Rust's rule of pointer
provenance, and Miri reported the undefined behaviour reproducibly. The
code comes from lean2rr's own patches: 13-b of
[issue 13](13-long-list-drop.md) adds the file, and 13-c rewrites it with
the same links. Upstream Reussir (`943f2195`) has no `drop.rs`.

The pending stack takes no memory per pending cell. A cell deferred with a
wide header (`__reussir_drop_defer_wide`) links to the cell deferred
before it, and the link is only the offset between the two cells, stored
in the later cell's header. When the drain pops the later cell, `unlink`
rebuilds the earlier cell's pointer as the later cell's pointer plus the
offset. The rebuilt pointer has the address of the earlier cell, but the
*provenance* of the later cell's allocation. The drain then releases the
later cell (which frees it) and afterwards gives the rebuilt pointer to the
earlier cell's release function, which reads and frees the earlier cell
through it. In Rust a pointer may access only the allocation that its
provenance comes from, so each of these accesses is undefined behaviour.
LLVM IR has the same rule: `wrapping_offset` is a `getelementptr` without
`inbounds`, whose result "may not necessarily be used to access memory".

No miscompile is known. The drain keeps the pointer in its thread-local
state and gives it to the release function through an indirect call, so
the optimizer does not see the accesses. A new compiler version or more
inlining can change that.

Found by a hunt of the runtime's release paths (finding HRT2-01), and
confirmed with Miri.

## Symptom and repro

Native runs give correct results. Under Miri, the release of the earlier
cell of a link is undefined behaviour when the two cells are separate
allocations, as they always are in a program (each cell is its own
mimalloc block).

Repro [`repros/bug47-unlink-provenance.rs`](repros/bug47-unlink-provenance.rs):
a Rust test of the checkout's `drop.rs` (which uses only `core` and
`std`), written as the `lib.rs` of a scratch crate. It defers two cells
with wide headers, each its own `Box`, so that they form one run, and then
drains:

```rust
let (a, b) = (cell(10), cell(20));     // two boxes: [count 1 | padding 0, id]
__reussir_drop_defer_wide(a, rel_box); // starts a run
__reussir_drop_defer_wide(b, rel_box); // b's header: the offset to a
assert_eq!(depth(), 1);                // one run: b links to a
__reussir_drop_drain();                // rel_box(b), then rel_box(a rebuilt from b)
// rel_box(p) reads the id at p + 8, then frees the box
```

The file also puts aside a box that lies 2^42 bytes or more from the next
one (a test thread can get its first boxes from another thread's heap),
because a cell that far from the cell before it starts a new run instead
of linking.

**Command.** The header of the file gives the commands: put the file as
`src/lib.rs` of a scratch crate, with copies of the checkout's
`crates/reussir-rt/src/drop.rs` and `drop/tests.rs`, then
`cargo +nightly miri test two_boxes_linked` (a nightly toolchain with the
`miri` component). `cargo test two_boxes_linked` runs it natively.
`run.sh` does not run it, because it needs Miri.

**Expected.** The test passes under Miri.

**Actual on `l2r-base2` (`71f17ae2`)** (and on every stack since 13-b;
the later patches keep `unlink`): the native test passes, in debug and
release builds. Miri (nightly-2026-08-31) stops in `rel_box`:

```
test bug47::two_boxes_linked ... error: Undefined Behavior: in-bounds pointer arithmetic failed: alloc44672 has been freed, so this pointer is dangling
  --> src/lib.rs:40:27
   |
40 |         let id = unsafe { p.cast::<u64>().add(1).read() };
   |                           ^^^^^^^^^^^^^^^^^^^^^^ Undefined Behavior occurred here
help: alloc44672 was allocated here:
  --> src/lib.rs:48:23
48 |         Box::into_raw(Box::new([1u64, id])).cast::<u8>()
help: alloc44672 was deallocated here:
  --> src/lib.rs:42:9
42 |         std::mem::drop(unsafe { Box::from_raw(p.cast::<[u64; 2]>()) });
   = note: stack backtrace:
           0: bug47::rel_box
           1: drop::State::drain       at src/drop.rs:328:26
           2: drop::drain_slow
           3: drop::__reussir_drop_drain
           4: bug47::two_boxes_linked
```

(Output shortened.) The pointer that `rel_box` gets for `a` has the
provenance of `b`, which `rel_box(b)` has just freed.

Reussir's own drop tests (`drop/tests.rs`) passed under Miri, also with
`-Zmiri-strict-provenance`: they take all their cells from one
allocation, so an offset never leads out of it.

**On `l2r-base2-47` (`b2e4a47e`), with the fix:** the native test
passes, and so does the test under Miri (nightly-2026-08-31, default
mode), with one warning: `integer-to-pointer cast` at
`with_exposed_provenance_mut` in `unlink`
(`-Zmiri-permissive-provenance` turns it off).

## Cause

`crates/reussir-rt/src/drop.rs` at `l2r-base2` (`71f17ae2`), function
`unlink`, lines 404 to 414:

```rust
unsafe fn unlink(cell: *mut u8) -> (*mut u8, u32) {
    let words = cell.cast::<u32>();
    let (low, high) = unsafe { (words.read(), words.add(1).read()) };
    unsafe {
        words.write(1);
        words.add(1).write(high & 0xffff);
    }
    let raw = (((high >> 16) as u64) << 24) | (low >> 8) as u64;
    let units = ((raw << (64 - OFFSET_BITS)) as i64) >> (64 - OFFSET_BITS);
    (cell.wrapping_offset(units as isize * 8), low & 0xff) // line 413
}
```

`wrapping_offset` keeps the provenance of `cell`, the linking cell.
`State::link` (lines 253 to 283), which `State::try_defer` calls for a
wide deferral (line 293), makes the link: it keeps only the distance
`(prev - cell) / 8` (line 265), as 40 bits in the header of `cell` (lines
276 to 280). The pointer `prev`, with its provenance, is not kept.

The path to the accesses: `__reussir_drop_drain` → `drain_slow` →
`State::drain` (lines 312 to 361). When the run on top has more than one
cell (`n > 1`, lines 320 to 326), the drain calls `unlink(head)` (line
321), makes the rebuilt pointer the new head (`self.head.set(prev)`, line
325) and calls `release(head)` for the linking cell (line 328), which
frees it. The next pass of the loop calls the earlier cell's release
function with the rebuilt pointer (line 328 again): Reussir's drop glue
(`drop_and_free_in_drain::<T>`, which reads the cell's fields and frees
the cell) or one of lean2rr's runtime functions (below).

## lean2rr

Nothing: lean2rr had no workaround, and needs none. Many frees of more
than one cell in lean2rr's programs run this code:

- Reussir's drop glue defers record boxes with a wide header through
  `__reussir_drop_defer_wide` (release function:
  `drop_and_free_in_drain::<T>`).
- lean2rr's runtime defers the cells of the payload types that it marks
  wide (`any::WIDE_BIT`) the same way (`drop::free_deferred_wide` in
  `runtime/leanrt/src/drop.rs`; release function: `l2r_any_rel_<num>_c`).
  A record deferred without a wide header (`drop::free_deferred`, release
  function `release_record`) can be the earlier cell of a link, and then
  gets a rebuilt pointer too.

## Fix (in 13-c)

Patch file [`patches/13-c-cheaper-pending-stack.patch`](patches/13-c-cheaper-pending-stack.patch)
(commit `bd733417` on `l2r-base2-47`). The fix costs nothing. It keeps
the address arithmetic, but takes the provenance from the earlier cell:
`State::link` exposes the provenance of `prev`, and `unlink` makes the
pointer from the address with the exposed provenance.

```rust
// State::link
// The link keeps only the offset to `prev`, another allocation than
// `cell`: [`unlink`] makes the pointer from the address, with the
// provenance exposed here.
let (at, to) = (cell.addr(), prev.expose_provenance());

// unlink
let prev = cell.addr().wrapping_add_signed(units as isize * 8);
(core::ptr::with_exposed_provenance_mut(prev), low & 0xff)
```

Before, `link` read the two addresses with `as usize` casts and `unlink`
returned `cell.wrapping_offset(units as isize * 8)`. The `as usize` cast
of `prev` already exposed its provenance; `expose_provenance()` says why.
`cell` needs only its address (`addr()`): the pointer to `cell` itself
stays in the state while it waits. `with_exposed_provenance_mut` gives
the new pointer the provenance of an exposed allocation that contains the
address, here the earlier cell's, which `link` exposed when it made the
link. The address computation is the same.

The test `linked_cells_in_separate_boxes` in `drop/tests.rs` is the
repro's test: two cells, each its own `Box`, deferred wide so that they
form one run, then drained. The other drop tests take all their cells
from one allocation, so Reussir's Miri job (`cargo miri test -p
reussir-rt`) now also covers cells in separate allocations.

**Why in 13-c.** 13-b added `drop.rs`; 13-c rewrote it and kept 13-b's
links, and the code fixed here is 13-c's. 13-b and 13-c were never
offered upstream (upstream Reussir has no `drop.rs`), so the fix is
folded into 13-c instead of a new patch at the end of the series. The
later patches apply unchanged: the series was rebuilt with
`git cherry-pick`, without conflicts. Of their files only 40-a's (the
other patch that changes `drop.rs` and `drop/tests.rs`) changes: its hunk
line numbers and blob hashes. The other files after 13-c are unchanged,
so their `From` lines still name the commits of `71f17ae2`'s history,
which have the same changes and messages.

**Checks** (2026-10-09):

- The rebuilt head `b2e4a47e` differs from `71f17ae2` only in the fix and
  the test (`drop.rs`: 10 lines added, 3 removed; `drop/tests.rs`: 46
  lines added). The series applied with `git am` on `943f2195` gives its
  tree, `350be937`.
- `cargo test -p reussir-rt`: the 47 tests pass, the new one among them.
- `cargo miri test -p reussir-rt drop` (default mode, stacked borrows):
  the five drop tests pass (`random_drops_match_the_model`, `digest`,
  `table_full`, `drained_runs_after_the_outermost_drain` and the new
  `linked_cells_in_separate_boxes`), with the one warning above; with
  `-Zmiri-tree-borrows` too. The repro passes under Miri. The new test on
  `71f17ae2`'s `drop.rs` (without the fix) makes Miri stop in
  `release_box` with "Undefined Behavior: in-bounds pointer arithmetic
  failed: alloc... has been freed".
- The release-mode machine code (aarch64; `libreussir_rt.a` of the CMake
  build) of `__reussir_drop_defer_wide`, of `drain_slow` and of the other
  eleven functions of the pending stack (`__reussir_drop_defer`,
  `__reussir_drop_drain`, `defer_slow`, `drain_one`, `grow`, ...) is
  identical to `71f17ae2`'s, symbol names included (`objdump`, addresses
  left out).
- lean2rr (dev `d52e6c34`) built against the rebuilt stack: leanrt's unit
  tests (82) pass; 26 runtime tests of frees and their order (the `RtDrop*` tests, `RtDepDropOrderBoxed`,
  `RtBorrowRelease*`, the `RtArray*Free*` tests, `RtNestedArrayFreeOrder`,
  `RtPromiseNestedFreeOrder`, `RtPromiseResolvedFreeOrder`,
  `RtListDropWhole`, `RtBoxDeepChain`, `RtBoxLeafRelease`,
  `RtBoxPackFreeOrder`, `RtArrayGetOobOrder`, `RtCArrInPlace`) give
  native's output; `tests/runtime/alloc-check.sh` passes on
  `RtListDropWhole` (all six modes: allocations within the allowed
  growth, peak memory below native's).
- With `-Zmiri-strict-provenance`, Miri stops at
  `with_exposed_provenance_mut` ("unsupported operation"). The drop tests
  now run under Miri's default provenance model only. Strict provenance
  cannot be kept at no cost: the stack would have to keep the pointer of
  each pending cell, which is the memory per cell that the links avoid.
  13-c's message and [issue 13](13-long-list-drop.md) are updated.

## Upstream note

Upstream Reussir has no pending stack, so there is nothing to report on
its own. The fix is part of 13-c; if 13-b and 13-c were proposed upstream,
it would go with them. Before the fix, `unlink` rebuilt the pointer of
the cell that a deferred cell links to from the linking cell's pointer
and an offset (`wrapping_offset`), so the pointer had the provenance of
the wrong allocation (Miri: undefined behaviour when the cells are
separate allocations).
`prev.expose_provenance()` in `link` and `with_exposed_provenance_mut` in
`unlink` fix it with the same machine code.
