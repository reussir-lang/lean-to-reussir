# 10. An opaque FFI handle cannot be an immediate

**Kind:** missing feature. Not a bug: Reussir does not promise handles
that may be a number instead of a pointer. lean2rr's box `LAny` needs
them (and its one-word `Nat` and `Int` did, until clean-integration D8 on
2026-10-26); patch 10-a adds them (*tagged* opaque handles).

## Summary

**Kind:** missing feature (lean2rr's prelude needs it). **Status:**
patched (10-a), applied in `./reussir` (`l2r-local` commit `a75ed2cf`).
lean2rr's prelude declares the box `LAny` `tagged` (until D8 also `Nat`
and `Int`); rrc rejects the attribute without the patch.

**Upstream (2026-10-24):** Not upstream at 0378b744: an opaque FFI handle must still be a pointer to a counted box. Upstream 0378b744 has built-in `Nat` and `Int` (#776 `af25863e`, with #770 to #803): rcgmp integers, where a small value is an immediate and a large one a counted heap object. They are another way to a one-word `Nat` and `Int`; since D8 (2026-10-26) lean2rr's `Nat` and `Int` are these built-in integers, and its prelude still needs 10-a for the box `LAny`. 10-a stays in the series on 0378b744, ea240b19 and 00906e38 (2026-10-25; it applies unchanged), and on `l2r-base10` (Phase 2: the first patch of the series, commit `6272aed4`; only line offsets change; its rebase onto 7954a367 had two conflicts: upstream added the `placement` and `launch` fields to records).

Until 2026-10-06 this patch had no entry: it was one of the two "local
additions" (file `local-additions.md`, now entries
9, retired on 2026-10-25, and 41).

## What is missing

An opaque Reussir record (`#[ffi(rust = "path")] pub struct T;`) is a
handle to a foreign, reference-counted box. Reussir copies such a handle by
incrementing the 32-bit count at offset 0 of the box, in line, and releases
it by calling a generated drop hook (the Rust type's `Drop`). Every handle
must be a pointer to such a box.

Until D8, lean2rr represented `Nat` and `Int` as one word, as Lean does
(today the box `LAny` is such a word: an odd word an immediate, an even
word a pointer to a counted cell). A small `Nat`
`n` (below 2^63) was the word `2n+1`, a small `Int` (the `int32` range)
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
generates (plan §5.1, "History: one-word `Nat` and `Int`", weighs the
options).

**Repro.** None in [`repros/`](repros/): without the patch rrc rejects the
attribute, and with it the Reussir tests below show the guarded count (see
[Checks and review](#checks-and-review)).

## Patch

Patch file
[`patches/10-a-tagged-ffi-objects.patch`](patches/10-a-tagged-ffi-objects.patch)
(`l2r-local` commit `a75ed2cf`, applied in `./reussir`; made as commit
`b4ea1ae1` in a scratch checkout on top of old 23-a (upstream #683), for the work of branch
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
  false (existing IR is unchanged). Since 2026-10-25 the type also has a
  builder with the two old parameters (`FFIObjectType::get(ctx, name,
  hook)` in `include/Reussir/IR/ReussirTypes.td`), which gives an untagged
  object: C++ code written for the type before `tagged` compiles
  unchanged. Upstream's C++ unit test `record_drop.cpp` builds the type
  that way; without the builder, Reussir's C++ unit tests (`reussir-ut`)
  do not compile. With it, all 82 pass on `l2r-base9` (on the bases with
  patch 02-b, that patch also updated upstream's `glue_symbols.cpp`).
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
  (`leanrt::any::LAny`'s `Drop` and `Clone` make the same test, as did
`leanrt::nat::LNat`'s until D8). Real boxes
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

**Effect on lean2rr.** Until D8, `Nat` and `Int` fields took 8 bytes
instead of 16, small values were never allocated, copying or dropping
one was a bit test; the box `LAny` keeps these properties for its
immediates.
(When arrays and references had a representation per element type, an
`Array Nat` without the `nat-arrays` pass was `RVec<Nat>`, one word per
element, and an `IO.Ref Nat` a cell holding the handle; since rule 1 they
hold boxes, `LAny`, which hold a small `Nat` as its own word.) lean2rr's
prelude needs the patch (rrc rejects the `tagged` attribute without it).

**Extension.** Patch 07-a ([issue 7](07-tagged-top-bits.md)) lets the
top 16 bits of a tagged pointer handle carry foreign data: `rc.inc` clears
them before it touches the count (lean2rr's one-word `Box` keeps its
payload's type number there). `Nat` and `Int` pointers had them clear
(until D8).

## Upstream note

The feature is general: any foreign type with a pointer-or-immediate
encoding (Lean objects, OCaml values, small-string optimizations) can use
it. A fuller version could let the foreign side choose the tag bit, or
lower the guard to a `select` where branches are costly.
