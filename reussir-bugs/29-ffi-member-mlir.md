# 29. The MLIR dump of a record with an `#[ffi]` member does not parse

## Summary

**Kind:** bug (tooling). **Status:** patched (0061), applied in `./reussir` (`l2r-local` cc8e5aa5).

**Verdict: bug.** The frontend writes a record member of an opaque
`#[ffi]` type as an explicit shared rc link, `!reussir.rc<!reussir.ffi_object<..>>`,
on purpose, and every pass handles it. The record type's verifier accepts
only *atomic* rc members, though. Types built in memory are not verified, so
compiling from source works, but the module `rrc --emit mlir` prints is
rejected when it is read back: "rc members must be atomic shared links; a
normal link is derived from the member's capability instead". Reussir
treats its stage dumps as resumable (`frontend/main_attribute.rr`: "a build
resumed from one of them is the build from source"); for these programs
they are not.

The finding as first reported named `[value]` records; it is wider: any
record (shared structures too) with an opaque member.

## Symptom and repro

Repro [`repros/bug29-ffi-member-mlir.rr`](repros/bug29-ffi-member-mlir.rr):
a structure `Holder(Vec<u64>, u64)` whose first member is an opaque
`#[ffi]` type (`reussir_rt`'s `Vec`); `main` prints `7`.

**Commands.**

    rrc bug29-ffi-member-mlir.rr --emit mlir -o a.mlir
    rrc a.mlir -x mlir --emit mlir -o b.mlir

**Expected.** The second command reads the dump back; `b.mlir` is
`a.mlir`.

**Actual on ef922049.** The second command fails:

    loc("-":5:170): error: rc members must be atomic shared links; a normal link is derived from the member's capability instead
    error: a.mlir: failed to parse MLIR module

(`reussir-opt a.mlir` fails the same way.) `run.sh` prints
`bug 29   REPRODUCES  the --emit mlir dump does not parse: rc members must
be atomic shared links`.

Every lean2rr program hits it: strings and arrays are FFI objects, and they
sit in lists, structures and constructor payloads. MapMIO
(a local example program), for example, fails on line 5,
a `[value]` payload `T_List.cons` holding an `LStr`.

## Cause

Codegen, `member_ty` (`crates/reussir-codegen/src/lower/ty.rs`):

```rust
// An opaque `#[ffi]` member cannot be spelled as a bare record
// (there is no inline layout); it is an explicit rc link, which
// the dialect stores as a pointer like any other rc member.
TyKind::Record { .. } if self.is_opaque_record(ty) => self.mlir_ty(ty),
```

`mlir_ty` of an opaque record is `!reussir.rc<!reussir.ffi_object<..>>`
with the normal (non-atomic) count. The dialect handles it: the member is
stored as a pointer (`memberStorageType`, `lib/IR/ReussirTypes.cpp`), and a
projection of it is the member type itself (`getProjectedType`).

`RecordType::verify` (`lib/IR/ReussirTypes.cpp`):

```c++
if (auto rcMember = llvm::dyn_cast<RcType>(member)) {
  // A member's *normal* shared link is derived from its capability, so a
  // plain rc member stays banned. An **atomic** shared link cannot be
  // derived ... so it is spelled explicitly as the member type.
  if (rcMember.getCapability() != Capability::shared ||
      rcMember.getAtomicKind() != AtomicKind::atomic) {
    emitError() << "rc members must be atomic shared links; a normal "
                   "link is derived from the member's capability instead";
```

The rule's reason, "a normal link is derived from the member's
capability", does not hold for an `ffi_object`, which has no capability:
a member of that type has to be spelled as an explicit link. The frontend
completes the record type without verification (`record_complete_in_place`
→ `reussirRecordTypeComplete`, `lib/CAPI/Types.cpp` →
`RecordType::complete`), so the check runs only when the parser builds the
type with `getChecked`.

## lean2rr

No effect on builds: `scripts/l2r.py` compiles from `.rr` and never
resumes from a dump. The dump of a lean2rr program could not be fed to
`reussir-opt` or back to `rrc -x mlir`, which is how one bisects a pass
problem by hand.

## Patch

Patch file
[`patches/0061-l2r-local-bug-29-accept-a-record-member-linking-to-a.patch`](patches/0061-l2r-local-bug-29-accept-a-record-member-linking-to-a.patch)
(`l2r-local` commit `83a49c66`, applied in `./reussir`; `l2r-local` head cc8e5aa5; made as commit `a4fabec4`
in a scratch checkout, after 0060, on which it does not depend). The verifier also accepts a shared rc member whose element
is an `ffi_object`:

```c++
+      bool ffiObjectLink =
+          rcMember.getCapability() == Capability::shared &&
+          llvm::isa<FFIObjectType>(rcMember.getElementType());
+      if (!ffiObjectLink &&
+          (rcMember.getCapability() != Capability::shared ||
+           rcMember.getAtomicKind() != AtomicKind::atomic)) {
+        emitError() << "rc members must be atomic shared links or shared "
+                       "links to an ffi_object; a normal link is derived "
+                       "from the member's capability instead";
```

and the `[field]` check that follows says "an rc member" instead of "an
atomic rc member", since it now covers both.

**Why it is correct.** The verifier now accepts exactly the type the
frontend already builds and the passes already handle; nothing that
compiled from source changes. Every other normal rc member is still
rejected (new test `basic/failure/record_rc_member.mlir`), as is an rc
member with the `[field]` capability.

**Verification.**

- Tests: `basic/success/record_ffi_object_member.mlir` (a shared structure
  and a `[value]` payload with an `ffi_object` link, printed and parsed
  twice), `basic/failure/record_rc_member.mlir`,
  `frontend/ffi_member_mlir_roundtrip.rr` (dump, read back, `diff`, compile
  the dump). The first and third fail on the unpatched build.
- The MapMIO dump (11 MB) reads back and prints identically. The LLVM IR
  built from the repro's dump is the IR built from its source, up to the
  hashes of the polymorphic-FFI crates (random per build).
- Reussir's lit suite and lean2rr's runtime tests: as for
  [bug 28](28-unique-carrying-join.md).
- `run.sh`: `bug 29   FIXED       the --emit mlir dump parses back and
  prints identically`.

**Review.** Round RV8 (e)
(local review notes): no defect. A
lean2rr dump (LeanBoolLoop, 9.2 MB, 5244 `ffi_object` occurrences) parses
back and prints identically; without 0061 it is rejected. The verifier
now accepts shared `rc<ffi_object>` members, normal or atomic, in
compound, `[value]` and regional records, and still rejects rigid and
flex ones, `[field]` rc members and normal `rc<record>` members. Side
note of the review: the rc type parser drops text after a comma
([bug 33](33-rc-trailing-text.md)).

**Effect on lean2rr.** None on builds; lean2rr's MLIR dumps become usable.

## Upstream note

`RecordType::verify` (`lib/IR/ReussirTypes.cpp`) rejects normal rc members,
but codegen's `member_ty` deliberately emits `rc<ffi_object>` for an opaque
`#[ffi]` member, so `rrc --emit mlir` output for any record with such a
member does not parse back. Fix: accept a shared rc member whose element is
an `ffi_object`.
