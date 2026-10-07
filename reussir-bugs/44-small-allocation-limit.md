# 44. The small-allocation fast path assumes 64-bit pointers

## Summary

**Kind:** bug (on 32-bit targets). **Status:** not patched; it does not
affect lean2rr (unreachable: lean2rr builds only for 64-bit targets).

**Verdict: bug.** For an allocation whose size is a constant, rrc emits
a call to `__reussir_allocate_small(size)` instead of
`__reussir_allocate(align, size)` when the size is at most 1024 bytes and
naturally aligned. The runtime's `__reussir_allocate_small` is
`mi_malloc_small`, which serves only sizes up to mimalloc's
`MI_SMALL_SIZE_MAX`, 128 pointers: 1024 bytes on a 64-bit target, but 512
on a 32-bit one. The limit of 1024 is fixed in the compiler, whatever the
target, and the runtime checks the size with a `debug_assert!` only. So on
a 32-bit target a box of 513 to 1024 bytes goes to `mi_malloc_small`,
which indexes the heap's table of small pages past its end (mimalloc does
not check in release builds): heap corruption.

Found by a review of Reussir's runtime crate (finding HRT-02).

## Symptom and repro

No repro in [`repros/`](repros/): it needs a 32-bit target, and lean2rr's
test machine and Reussir's builds are 64-bit (aarch64, x86-64). A record of
600 bytes, allocated as a box, built for a 32-bit target (for example
`armv7` or `i686`), would show it.

## Cause

The contract is written down on both sides with the 64-bit value:

- `include/Reussir/Support/AllocatorBinModel.h`:
  `inline constexpr std::size_t kSmallAllocationLimit = 1024;`, whose
  comment says it is mimalloc's `MI_SMALL_SIZE_MAX` (128 *
  `sizeof(void*)`): true only for 8-byte pointers.
- `lib/Conversion/BasicOpsLowering/BasicOpsLowering.cpp` (the lowering of
  a token allocation): `alignment <= 8 && size % alignment == 0 && size <=
  kSmallAllocationLimit` selects `__reussir_allocate_small`.
- `crates/reussir-rt/src/alloc.rs`: `alloc_small` checks `size <=
  ffi::MI_SMALL_SIZE_MAX` with `debug_assert!` and calls
  `mi_malloc_small`; its comment says that the precondition is
  "load-bearing" because mimalloc does not check it in release builds.
  `libmimalloc-sys` defines `MI_SMALL_SIZE_MAX` as `128 *
  size_of::<*mut c_void>()`.

A fix takes the limit from the target: 128 times the target's pointer
size (the data layout rrc already has), or the smaller of the two values.

## lean2rr

Not affected, and not reachable: lean2rr builds only for 64-bit targets
(its runtime, leanrt and lean-runtime, assume 64-bit words, as Lean's
`Nat` encoding does), where the two limits are both 1024.

## Why it stays unpatched

No patch (the owner's rule since 2026-10-07: Reussir is changed only where
lean2rr has no other way; lean2rr does not reach this code).

## Upstream note

`kSmallAllocationLimit` (`include/Reussir/Support/AllocatorBinModel.h`)
is 1024, mimalloc's `MI_SMALL_SIZE_MAX` on 64-bit targets only; on 32-bit
targets that maximum is 512, and `__reussir_allocate_small`
(`mi_malloc_small`, size checked by `debug_assert!` only) then gets sizes
it must not. The limit should be `128 * pointer size` of the target.
