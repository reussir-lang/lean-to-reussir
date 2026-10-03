# 1. `[value]` enum payloads lost in the LLVM lowering

## Summary

**Kind:** bug. **Status:** patched (0020), applied in `./reussir`
(`l2r-local` 5c0514e3). lean2rr's output was never affected: it emits only
unaffected `[value]` enums.

A `[value]` enum is moved as the LLVM struct of one "representative" arm,
so another arm's bytes that fall on that arm's padding or on an `i1` field
are lost when the value is moved: wrong values, or a pointer losing its
upper bytes.

## Symptom and repro

Repro [`repros/bug01-value-enum-payload.rr`](repros/bug01-value-enum-payload.rr):

```
enum [value] M { A(u8), B(bool) }
#[ffi(import)]
fn say(x : u8) [{ println!("{}", x) }];
#[main]
fn main() {
    let m = M::A{42};
    match m { M::A(x) => { say(x) }, M::B(v) => { say(7) } }
}
```

**Command.** `rrc bug01-value-enum-payload.rr -O default`, then run it.

**Expected.** `42`.

**Actual on ef922049.** `0`, at every optimization level: only bit 0 of 42
survives (43 gives 1). With a nested `[value]` enum on the padding, a
pointer can lose its upper bytes (SIGSEGV). `run.sh` printed
`bug 01   REPRODUCES  prints 0, expected 42   [-O default]`; with 0020
(the final stack) it prints `bug 01   FIXED       prints 42   [-O default]`.

## Cause

A `[value]` enum is lowered to the LLVM struct `{ tag,
<representative arm> }`. The representative arm is the last arm with the
largest alignment (`lib/IR/ReussirTypes.cpp`, used by
`lib/Conversion/TypeConverter/TypeConverter.cpp`); here `B`, whose payload
is `{ i1 }`. The whole variant is moved as a first-class aggregate of that
type: by the `record.variant` lowering (store into an alloca, then load the
whole struct, `lib/Conversion/BasicOpsLowering/BasicOpsLowering.cpp`), by
passing arguments by value, and by `ref.spilled`. Bytes of another arm that
fall on padding inside the representative arm's struct, or on an `i1`
field, do not survive the move. (If the representative is shorter than
the largest arm, `convertRecordType` adds an explicit `i8` array for the
rest; those bytes are copied.)

## lean2rr

lean2rr emits only `[value]` enums that are unaffected: enumerations
without fields, and `Nat`/`Int`, whose arms each hold one 64-bit word.
Other multi-arm types are shared enums, and multi-field value records are
`[value]` structs, whose padding is explicit (plan §10).

The patch does not change lean2rr's code: the `[value]` enums it emits
(field-less enumerations, `Nat`, `Int`) keep their LLVM types, and lean2rr
keeps its rule (README policy: workarounds stay, so that lean2rr also works
with an unpatched Reussir).

## Patch

Patch file
[`patches/0020-l2r-local-bug-1-keep-every-arm-s-bytes-when-a-value-.patch`](patches/0020-l2r-local-bug-1-keep-every-arm-s-bytes-when-a-value-.patch)
(`l2r-local` commit `d1fbe33b`, applied in `./reussir`; `l2r-local` head
`5c0514e3`). It needs 0018 ([bug 8](08-padding-lift.md)), applied before
it.

**The change.** `convertRecordType`
(`lib/Conversion/TypeConverter/TypeConverter.cpp`) still lays a `[value]`
variant out as `{ tag, payload }`, with the same size, alignment and
payload offset, but the payload's LLVM type is no longer always the
representative arm. A new helper, `opaquePayloadType`, replaces it by an
array of alignment-sized integers of the payload's size
(`[size / align x i<8 * align>]`) when two conditions hold: more than one
arm has bytes, and the representative does not carry every byte of its
storage. A second helper, `carriesAllBytes`, decides the latter: an
integer whose width is a multiple of 8 and a pointer carry all their
bytes; a struct does if its members do and leave no padding; an `i1`,
padding, floating-point and vector values do not (the last two
conservatively).

```c++
-    auto [size, _unused, representative] =
+    auto [size, alignment, representative] =
         type.getElementRegionLayoutInfo(dataLayout);
     if (representative) {
-      members.push_back(converter.convertType(representative));
-      ...
+      mlir::Type payload = converter.convertType(representative);
+      // Fused-header (shared) variants are accessed through their boxes ...
+      mlir::Type opaque =
+          type.hasFusedHeader()
+              ? mlir::Type{}
+              : opaquePayloadType(type, payload, size, alignment, dataLayout);
+      if (opaque) {
+        members.push_back(opaque);
+      } else {
+        members.push_back(payload);
+        ... // the representative plus an i8 array for the rest, as before
```

For the repro, `M`'s payload `{ i1 }` (arm `B`) becomes `[1 x i8]`, which a
first-class load and store copy whole.

**Why it is correct.** The array has the payload's size and alignment, so
every offset and size Reussir computes is unchanged. Every access to an arm
goes through a GEP to the payload member and then uses the arm's own LLVM
type (`record.coerce`, `record.variant`, `rc.create_variant`, `record.tag`),
so field reads and writes do not change; no lowering does `extractvalue` or
`insertvalue` into a payload. Only the moves of whole variants (the
`record.variant` alloca round trip, arguments, spills, fields) see the new
type, and an array of integers carries every byte through them. Shared
(fused-header) variants keep their representative: their values exist only
between construction and the `rc.create` that boxes them, which
`RcCreateFusion` turns into per-field stores. `[value]` records do not
cross the FFI, and export trampolines take records by pointer, so no
calling convention changes. The arm's LLVM struct must fit in the payload,
which needs the declaration-order layout to agree with Reussir's: that is
0018.

**Verification.**

- Test `tests/integration/frontend/value_enum_payload_bytes` (with a C
  driver): `A(u8)` against `B(bool)`, a `u64` over a nested value enum's tag
  padding, a pointer there; at `-O default`, `-O aggressive` and with
  `--no-pack-record-members`, plus FileCheck of the LLVM type. It fails
  without the patch.
- `run.sh` on the final stack: `bug 01   FIXED       prints 42   [-O default]`.
- lean2rr: the LLVM type definitions of LeanBoolLoop, RtReprFuzzTypes and
  RtExistPayloads are identical with and without 0018-0021 (95, 207 and 541
  types; review below).
- On the final stack (all 34 patches): Reussir's lit suite, 645 tests, 564
  passed, 81 unsupported, none failed.

**Review.** Round 8 (`~/Documents/l2r-scratch/rv8/reussir/FINDINGS.txt`):
no correctness defect in 0018-0021. Checked: every access to an arm goes
through a GEP to the payload member and then the arm's type, and no
lowering does `extractvalue`/`insertvalue` into a variant payload; `[value]`
records are rejected at the FFI, polymorphic textures included; partly
filled alignment words (`A(u8)` in `[2 x i64]`, a three-arm enum with
`u8,u16` / `u64,bool` / `u32` arms) with black-boxed inputs, at `-O none`,
default and aggressive, with `--no-pack-record-members` and with `-g`,
introduce no poison; the interaction with 0022 (an opaque-payload enum
yielded from a `Nullable` match); closures that capture, take and return
such enums; a 16-aligned payload (`{i128, i1} | {i8, i1}` becomes
`{i8, [2 x i128]}`, 48 bytes, Reussir's layout); single-arm, zero-size-arm
and `i1` cases. [Bug 26](26-launder-assume.md) (an `llvm.assume` after the invariant-group
launder, patch 0021) was found by the differential fuzzing of 0018-0020; it
is not caused by them.

**Effect on lean2rr.** None on its current output (its `[value]` enums keep
their types). `[value]` enums with arms of different layouts become usable,
should lean2rr emit them.

## Upstream note

`convertRecordType` (`TypeConverter.cpp`) types a `[value]` variant's
payload as its representative arm, and variants move as first-class
aggregates, so another arm's bytes on the representative's padding or on an
`i1` are lost (`enum [value] M { A(u8), B(bool) }`: `A(42)` reads 0). Fix:
when the representative does not carry every byte and more than one arm has
bytes, type the payload as an array of alignment-sized integers of the same
size and alignment; accesses already go through the arm's own type.
