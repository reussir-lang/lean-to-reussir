# 41. An opaque FFI handle cannot be an immediate

**Kind:** missing feature. Not a bug: Reussir does not promise handles
that may be a number instead of a pointer. lean2rr's one-word `Nat` and
`Int` need them; patch 41-a adds them (*tagged* opaque handles).

## Summary

**Kind:** missing feature (lean2rr's prelude needs it). **Status:**
patched (41-a), applied in `./reussir` (`l2r-local` commit `a75ed2cf`).
lean2rr's prelude declares `Nat` and `Int` `tagged`; rrc rejects the
attribute without the patch.

Until 2026-10-06 this patch had no entry: it was one of the two "local
additions" (file `local-additions.md`, now entries
[40](40-drain-end-hook.md) and 41).

## What is missing

An opaque Reussir record (`#[ffi(rust = "path")] pub struct T;`) is a
handle to a foreign, reference-counted box. Reussir copies such a handle by
incrementing the 32-bit count at offset 0 of the box, in line, and releases
it by calling a generated drop hook (the Rust type's `Drop`). Every handle
must be a pointer to such a box.

lean2rr represents `Nat` and `Int` as one word, as Lean does. A small `Nat`
`n` (below 2^63) is the word `2n+1`, a small `Int` (the `int32` range)
`lean_box` of its 32 bits; a big one is a pointer to a counted big number
(lean2rr's own layout, one block with the limbs inline). The words are
Lean's own representation, and Lean's C runtime makes the same low-bit test
before every count update (`lean_inc`, `lean_dec`). Before the patch, `Nat`
was a two-word `[value]` enum `{ Small(u64), Big(LBig) }`: 16 bytes in
every record field (natively 8), and `Std.TreeMap Nat Nat` used about 1.5x
native memory. lean2rr cannot skip the counting of small values itself:
Reussir inserts it (in records, closures, enums, its drop and acquire
glue). Without the feature, Reussir would increment "the count" of a small
`Nat` at address `2n+1`, a crash. A clone hook would be the same mechanism
with a call per copy, and lean2rr cannot change the drop glue Reussir
generates (plan §5.1, "One-word `Nat` and `Int`", weighs the options).

**Repro.** None in [`repros/`](repros/): without the patch rrc rejects the
attribute, and with it the Reussir tests below show the guarded count (see
[Checks and review](#checks-and-review)).

## Patch

Patch file
[`patches/41-a-tagged-ffi-objects.patch`](patches/41-a-tagged-ffi-objects.patch)
(`l2r-local` commit `a75ed2cf`, applied in `./reussir`; made as commit
`b4ea1ae1` in a scratch checkout on top of 23-a, for the work of branch
`mem-nat`).

The patch adds an opt-in flag, `#[ffi(rust = "path", tagged)]`: a handle of
such a type may also be an odd word that is not a pointer at all, and
Reussir then increments the count, or calls the hook, only when the
handle's low bit is clear.

### Where in Reussir

- Frontend: the attribute is parsed in `crates/reussir-core/src/semi/ctxt.rs`
  (`Record::ffi_tagged`) and travels through the textual HIR
  (`{ ffi tagged "path" }`; the shared IR lexer's `tagged` keyword is also
  accepted as a name), the package interface, monomorphization into
  the MIR layout (`RecordLayout::Opaque { tagged }`, printed
  `{ "path", @hook, tagged }`) and codegen
  (`crates/reussir-codegen/src/lower/ty.rs`, through the C API
  `reussirFFIObjectTypeGet(..., tagged)`).
- Dialect: `FFIObjectType` gets a default-valued `bool` parameter, printed
  `!reussir.ffi_object<"path", @hook, tagged = true>` and omitted when
  false (existing IR is unchanged).
- Lowering (`lib/Conversion/BasicOpsLowering/BasicOpsLowering.cpp`, the only
  place where `rc.inc` and `rc.dec` of an `ffi_object` become code):
  `beginRealBoxGuard` splits the block on `(ptrtoint p) & 1 == 0`; the
  increment and the call to the cleanup hook go in the guarded block, and
  nothing is loaded from the handle before the test.
- The two other places that read the count of an arbitrary rc value skip
  tagged objects: the optional `--instrument-nonlinear-ffi` check and the
  uniqueness-carrying analysis (`rc.assume_unique` on a carried argument;
  it cannot fire for an FFI object, which Reussir never creates fresh, but
  is excluded anyway). Nothing else reads through an opaque handle: an
  `ffi_object` produces no reuse token, is not deferred by the drop glue,
  and reaches foreign code only as its Rust type, which knows the encoding
  (`leanrt::nat::LNat`'s `Drop` and `Clone` make the same test). Real boxes
  are at least 4-aligned (the count is a `u32` at offset 0), so the low bit
  of a real handle is always clear, and an immediate (odd) is never null.

### Checks and review

Tests: `conversion/tagged_ffi_object.mlir` (guarded `rc.inc`/`rc.dec` for a
tagged object, unguarded for an untagged one, the textual form),
`conversion/instrument_nonlinear_ffi_tagged.mlir`, `frontend/ffi_tagged.rr`
(the attribute through HIR, MIR and MLIR), HIR and MIR round-trip unit
tests; all `reussir-core` unit tests (467) and the existing FFI tests
(`instrument_nonlinear_ffi.mlir`, `ffi_vec.rr`, `rc_delta.mlir`) pass
unchanged. On lean2rr: the runtime suite, the classic corpus, the Reussir
benchmark suite, the round-7 big-number repros, and tests of every
`Nat`/`Int` operation at 2^62, 2^63 and 2^64 and of `Nat`s in every
container, including counted big-number allocations and frees
(`tests/runtime/nat-alloc-check.sh`: `RtNatStress`, also through
`IO.Ref` set/swap/modify, and `RtNatConst`).

Reviews: the mem-nat review (local review notes,
`mem/nat/review/FINDINGS.txt`) and round RV8 (local review notes,
`rv8/nat/FINDINGS.txt`, Q3) found no defect in the patch: the guard covers
the delta, atomic and immortal-steering paths of `rc.inc`; `rc.dec` calls
the hook only for an even word (and the hook re-tests it); every other
reader or writer of a count was traced to a guarded path or excludes FFI
objects; Reussir puts no alignment or dereferenceable attributes on FFI
handles, so LLVM cannot fold the low-bit test away. The first review's
optional hardening (exclude tagged objects from `rc.assume_unique`) is in
the final patch.

**Effect on lean2rr.** `Nat` and `Int` fields take 8 bytes instead of 16,
small values are never allocated, copying or dropping one is a bit test.
(When arrays and references had a representation per element type, an
`Array Nat` without the `nat-arrays` pass was `RVec<Nat>`, one word per
element, and an `IO.Ref Nat` a cell holding the handle; since rule 1 they
hold boxes, `LAny`, which hold a small `Nat` as its own word.) lean2rr's
prelude needs the patch (rrc rejects the `tagged` attribute without it).

**Extension.** Patch 38-a ([issue 38](38-tagged-top-bits.md)) lets the
top 16 bits of a tagged pointer handle carry foreign data: `rc.inc` clears
them before it touches the count (lean2rr's one-word `Box` keeps its
payload's type number there). `Nat` and `Int` pointers have them clear.

## Upstream note

The feature is general: any foreign type with a pointer-or-immediate
encoding (Lean objects, OCaml values, small-string optimizations) can use
it. A fuller version could let the foreign side choose the tag bit, or
lower the guard to a `select` where branches are costly.
