# 8. A padding "lift" breaks declaration-order layouts

## Summary

**Kind:** bug. **Status:** patched (0018), applied in `./reussir`
(`l2r-local` cc8e5aa5). It does not affect lean2rr (it never emits the
shape).

Under `--no-pack-record-members`, a member followed by padding is widened
to an integer that covers the padding, which can give LLVM a larger (more
aligned) layout than the one Reussir allocates: a heap overflow, and field
offsets on which Reussir and LLVM disagree.

## Symptom and repro

Repro [`repros/bug08-padding-lift.rr`](repros/bug08-padding-lift.rr):

```
struct [value] S3(u8, u8, u8)
struct [value] Q(S3, u16)
struct R(Q, Q, Q, Q, Q, Q, u16)
enum L { Nil, Cons(R, L) }
...
fn build(n : u64, acc : L) -> L { if n == 0 { acc } else { build(n - 1, L::Cons{R{mkq(n), ..., (n % 50000) as u16}, acc}) } }
fn sum(l : L, acc : u64) -> u64 { match l { L::Nil => { acc }, L::Cons(r, t) => { sum(t, acc + (r.6 as u64) + (r.5.1 as u64) + (r.0.0.2 as u64)) } } }
#[main]
fn main() { say(sum(build(100000, L::Nil{}), 0)); }
```

**Command.** `rrc bug08-padding-lift.rr -O aggressive --no-pack-record-members`.

**Expected.** `2550200000`.

**Actual on ef922049.** SIGSEGV (a heap overflow). With the default
(packed) layout it prints `2550200000`. `run.sh` printed `bug 08
REPRODUCES  SIGSEGV (cells overflowed), expected 2550200000`; on the final
stack it prints `bug 08   FIXED       prints 2550200000   [-O aggressive
--no-pack-record-members]`.

## Cause

`lib/Conversion/TypeConverter/TypeConverter.cpp`, `convertRecordType`:
under `--no-pack-record-members`, a member followed by padding is widened
to an integer that covers the padding, without checking that this integer
is no more aligned than the next member. Reussir's layout of `Q` is 6
bytes with alignment 2; its LLVM type `{ i32, i16 }` is 8 bytes with
alignment 4. `R` is a shared struct, so each `R` lives in its own cell
(the list cell `L::Cons` holds two pointers and is not affected). Reussir's
`R` is 38 bytes, and it allocates each `R` cell (the 4-byte count plus
`R`) as 44 bytes; LLVM's `R` is 52 bytes, and the cell is written through
`{ i32, R }`, 56 bytes, so every `R` cell is written past its end. In
`rrc --emit mlir-llvm` (the flags above): `!llvm.struct<"_RC1Q", (i32, i16)>`,
`llvm.call @__reussir_allocate_small(%2)` with `%2 = 44`, then stores into
fields 0 to 6 of `!llvm.struct<(i32, struct<"_RC1R", ...>)>`; `L::Cons` is
`(ptr, ptr)`. Reussir's and LLVM's field offsets also
disagree: when a cell of `struct R1(Q, u16)` is reused for
`struct R2(S6, u16)` (`S6` = three `u16`) and the store of the `u16` is
skipped ([bug 2](02-reuse-field-store.md)), `R2.1` reads the wrong bytes
(`300000` instead of `305000`; with 0002 the store is no longer skipped
there). The packed layout sorts members by alignment and never needs the
lift.

## lean2rr

Never produces this shape: its records have no padding between members
(fields in decreasing alignment), and its `[value]` structs have a single
field whose size is a power of two.

## Patch

Patch file
[`patches/0018-l2r-local-bug-8-widen-a-member-over-its-padding-only.patch`](patches/0018-l2r-local-bug-8-widen-a-member-over-its-padding-only.patch)
(`l2r-local` commit `599064fb`, applied in `./reussir`; `l2r-local` head
`cc8e5aa5`).

**The change.** One condition in the lift of `convertRecordType`
(`lib/Conversion/TypeConverter/TypeConverter.cpp`, compound branch): the
integer that covers a member and its padding must be no more aligned than
the next member (`align`).

```c++
           if (lastMemberSize < liftCandidateSize &&
-              lastMemberSize + lastMemberNeedToPad == liftCandidateSize) {
+              lastMemberSize + lastMemberNeedToPad == liftCandidateSize &&
+              dataLayout.getTypeABIAlignment(liftCandidate) <= align) {
```

Otherwise the member is padded explicitly (`{ member, [pad x i8] }`), as
when no integer has the right size. In the repro, `S3` before a `u16` is no
longer lifted to `i32` but padded explicitly, so LLVM's `Q` is 6 bytes with
alignment 2, Reussir's layout. Records whose lift already met the condition
(a `u8` before a `u16` or an `i64`) are converted as before.

**Why it is correct.** Under declaration order every padding run is
absorbed into the member before it, so each LLVM member starts where the
previous one ends. With the integer's alignment at most the next member's,
both the next member's offset and the integer's size are multiples of the
integer's alignment, so the integer starts at the previous member's offset
(Reussir's), and it cannot raise the record's alignment. The record's size
is unchanged (tail padding is explicit, and LLVM's alignment is at most
Reussir's). The packed layout sorts members by descending alignment and
never pads between them, so it is untouched.

**Verification.**

- Test `tests/integration/frontend/record_lift_alignment` (with a C
  driver): records with lifted and padded members under
  `--no-pack-record-members`, the LLVM types checked with FileCheck, built
  and run at `-O default` and `-O aggressive`. It fails without the
  patch.
- `run.sh` on the final stack: `bug 08   FIXED       prints 2550200000`.
- On the final stack (all 34 patches): Reussir's lit suite, 645 tests, 564
  passed, 81 unsupported, none failed.

**Review.** Round 8 (local review notes):
no correctness defect. The reviewer proved the invariant above (the next
offset and the lifted size are multiples of the integer's alignment, so it
starts at Reussir's offset), checked that the lift never lowers the
previous member's alignment, that packed mode is untouched and that
zero-sized members cannot occur, and ran `t/l1.rr` (a `bool` lifted to
`i16`, `S3` lifted to `i32` before a `u64`, a `u8` before a 16-aligned
record, `S3` padded before a `u16`) in both layouts at `-O none` and
aggressive: the independently computed result everywhere, and LLVM types
of Reussir's sizes (for example `R4 = {R1, i16, R3, i1, [7 x i8]}`,
32 bytes). `record.compound` stores each member with its own type, so a
lifted or padded member is stored correctly. The fix was written when the
review of the first versions of the patches for bugs 1 and 2 (variants)
showed that they, computing offsets from Reussir's layout, need it to
agree with LLVM's; 0020 needs this patch.

**Effect on lean2rr.** None: its records have no padding between members.

## Upstream note

`convertRecordType` (`TypeConverter.cpp`), declaration-order layout: a
member followed by padding is widened to an integer covering the padding
without checking that the integer is no more aligned than the next member.
`struct [value] S3(u8, u8, u8)` before a `u16` becomes `i32`, so LLVM's
record is larger and more aligned than the one Reussir allocates (a heap
overflow; offsets disagree). Fix: widen only to an integer whose ABI
alignment is at most the next member's, else pad explicitly.
