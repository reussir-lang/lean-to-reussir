# 38. The inline count increment of a tagged handle uses all 64 bits as the address

**Kind:** missing feature. Not a bug: patch 41-a (tagged opaque handles,
[issue 41](41-tagged-ffi-objects.md)) promised only that an odd handle is an immediate. Patch 38-a extends it:
the top 16 bits of a pointer handle may carry foreign data.

## Summary

**Kind:** missing feature (lean2rr's one-word box needs it). **Status:**
patched (38-a), not yet applied in `./reussir`; lean2rr's generated code
does not use the feature yet (the probe of the one-word `Box`, track E of
the dependent-type work, does).

lean2rr's one-word `Box` (`leanrt::any::LAny`, runtime/prelude.rr section
"The one-word box") is a `tagged` opaque type. An odd word is an
immediate; an even word is a pointer to a counted object whose low 48 bits
are the address and whose top 16 bits are the number of the payload's type
(the drop hook dispatches on it). Reussir copies a tagged handle with an
inline increment of the `u32` count at the handle's address. With the
number in the top bits, that address is not the object's: the increment
faults.

## Symptom and repro

Repro [`repros/bug38-tagged-top-bits.rr`](repros/bug38-tagged-top-bits.rr):

```
#[ffi(rust = "::reussir_rt::rc::Rc<u64>", tagged)]
pub struct Word;
// make(x): a new Rc of x, its handle or-ed with 5 << 48.
// take(w): the handle without its tag; 10 * value + count; released.
fn main() {
    let w = make(7);
    let a = take(w);   // w is used again: Reussir increments its count first
    let b = take(w);
    say(a + b);
}
```

**Command.** `rrc bug38-tagged-top-bits.rr -O aggressive` (with the
polymorphic-FFI directories, as `run.sh` passes them).

**Expected.** Prints `143` (count 2 at the first `take`, 1 at the second).

**Actual on `l2r-local` d79f8b70** (with patch 41-a): killed by SIGSEGV at
the increment. `run.sh` prints `issue 38   REPRODUCES  a tagged handle with
top bits copied in line: killed by SIGSEGV   [-O aggressive]`.

## Cause

`ReussirRcIncConversionPattern` (`lib/Conversion/BasicOpsLowering/BasicOpsLowering.cpp`)
lowers `rc.inc` of an `ffi_object` to a load and a store of the `u32` at
the handle itself (patch 41-a adds the guard that skips odd handles). The
hardware does not mask bits 48 to 55 (aarch64's top-byte-ignore covers bits
56 to 63 only; x86-64 masks nothing), so a handle with any of the top 16
bits set is not a valid address.

## lean2rr

Not used by generated code yet. lean2rr's `Nat` and `Int` are tagged too;
their pointers come from mimalloc and have the top 16 bits clear (see
below), so 38-a changes nothing for them but one AND on the increment of a
big number. The probe of the one-word box (a hand-written program over the
prelude: records, enums, function values, strings, arrays of boxes,
references, cells, big numbers, a chain of 10^6 nested boxes) needs 38-a:
built against `l2r-local` d79f8b70 it is killed by SIGSEGV at the first copy
of a boxed pointer; with 38-a it runs and frees every allocation exactly
once.

## Patch

Patch file
[`patches/38-a-tagged-top-bits.patch`](patches/38-a-tagged-top-bits.patch)
(commit `3350bc38` on branch `l2r-anybox` of a scratch Reussir worktree,
made on `l2r-local` d79f8b70). Issue number 37 is left to another
track's patch (value records across the FFI boundary), which reserved it
(with the old patch number 0067; its file will be `37-a-*.patch`).

`taggedBoxAddress` returns the handle with its top 16 bits cleared, as an
`llvm.ptrmask` with `2^48 - 1` (the provenance is kept), on 64-bit targets;
on narrower targets it returns the handle. `rc.inc` of a tagged
`ffi_object` uses it as the count's address, inside patch 41-a's guard
(even words only), on every path: the plain increment, the increment by a
delta, the atomic one. `rc.dec` is unchanged: the cleanup hook gets the
handle with its top bits, so the foreign side keeps its own encoding. The
dialect type's description and the C API comment say so.

**Why it is correct.** The mask runs only on a handle that the guard
classified as a pointer, and only for the count's address. For a handle
without top bits it is the identity. Nothing else reads through a tagged
handle (patch 41-a's review traced every reader of a count: the
decrement calls the hook; the nonlinear-FFI instrumentation and the
unique-carrying analysis skip tagged objects; an `ffi_object` gets no
reuse token and no deferred release). User-space addresses fit in 48 bits
on the targets lean2rr builds for: aarch64 Linux with 48-bit virtual
addresses (with 52-bit ones, the kernel gives an address above 2^48 only
to a mapping asked for above it), x86-64 with 47-bit user space (5-level
paging likewise only on request); mimalloc's address hints lie between 2
and 32 TiB. leanrt checks the 48-bit assumption when it boxes a pointer
(a panic).

**Verification.**

- `tests/integration/conversion/tagged_ffi_object.mlir`: the mask before
  the load and the store, also with a delta and before the `atomicrmw` of
  an atomic count; no mask for an untagged object; the hook gets the
  unmasked handle. It fails on d79f8b70 (no
  `llvm.ptrmask`) and passes with 38-a. The other conversion tests that
  mention `ffi_object`, `rc.inc` or `tagged` (62 files, run by their RUN
  lines) give the same results with and without the patch;
  `frontend/ffi_tagged.rr` and `conversion/instrument_nonlinear_ffi_tagged.mlir`
  pass.
- `run.sh`: `issue 38   FIXED       a tagged handle with top bits copied in
  line: prints 143   [-O aggressive]`.
- The probe of the one-word box (see lean2rr): every scenario frees every
  block it allocates exactly once; the copy of a box is an inline `and`,
  load, add and store (no call).

**Review.** An independent review of the one-word box (local review
notes `review-anybox/r1`, 2026-10-06) found no defect in the patch. It
asked for the atomic case in the test, which the patch now checks
(Reussir commit `3350bc38`, test only).

**Upstream note.** A general form would let the foreign type name the bits
that are not part of the address (a mask), or the number of address bits.
