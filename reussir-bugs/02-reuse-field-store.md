# 2. In-place reuse skips stores of fields that sit elsewhere in the new record

## Summary

**Kind:** bug. **Status:** patched: structures by 0002, variants by 0019,
both applied in `./reussir` (`l2r-local` cc8e5aa5). lean2rr also works
around the variant half (it turns member packing off).

When a function consumes a record and builds another of the same size,
Reussir writes the new record into the old cell (token reuse). Its copy
avoidance then skips the store of any field i whose new value was just
read from field i of the old cell, assuming the bytes are already in place
(`lib/Transformation/RcCreateFusion/RcCreateFusion.cpp`). Two cases get the
offset wrong, and the new record keeps whatever bytes the old one had
there: a wrong value with no error.

- **Structures:** the check compares only the field *index*, not the two
  types. In a different structure type, field i can sit at a different
  offset, under any layout. Patch 0002 skips such stores only when the old
  and new cells have the same type.
- **Variants:** the check compares the member types at indices 0..i, which
  implies equal offsets under declaration order but not under Reussir's
  default packed layout. Patch 0019 also requires field i to sit at the
  same byte offset from the box. lean2rr avoids the case with a flag, and
  keeps the flag.

## Symptom and repro

### Structures

Repro [`repros/bug02a-struct-reuse.rr`](repros/bug02a-struct-reuse.rr):

```
struct A(u64, u32)
struct B(u32, u32, u64)
#[ffi(import)]
fn say(x : u64) [{ println!("{}", x) }];
#[ffi(import)]
fn five() -> u32 [{ 5 }];
fn f(a : A) -> B { B{7, a.1, 9} }
fn g(b : B) -> u64 { (b.0 as u64) * 1000000 + (b.1 as u64) * 1000 + b.2 }
#[main]
fn main() { say(g(f(A{123, five()}))); }
```

**Command.** `rrc bug02a-struct-reuse.rr -O aggressive --no-pack-record-members`.

**Expected.** `7005009`, that is `B{7, 5, 9}`.

**Actual on ef922049.** `7000009`, at every `-O` level, with and without
`--reuse-across-call` and `--no-pack-record-members`. `run.sh` printed
`bug 02a  REPRODUCES  prints 7000009, expected 7005009   [-O aggressive --no-pack-record-members]`.

With declaration-order layout, `A` has `u64` at payload offset 0 and `u32`
at 8. `B` has `u32` at 0, `u32` at 4 and `u64` at 8. Both are 16-byte
payloads, so `f`'s `B` reuses `a`'s cell. `B.1 = a.1` is a load of field 1
of the old cell, so the store of `B.1` (offset 4) is skipped because its
value is a load of `A.1` (offset 8). `B.1` then reads bytes 4..8 of the old
payload, the high half of `A.0 = 123`, which is 0.

In Lean terms, with lean2rr's field order:

```lean
structure P where a : UInt64; b : UInt64; c : UInt32
structure Q where a : UInt64; b : UInt32; c : UInt32; d : UInt32; e : UInt32
@[noinline] def conv (p : P) : Q := { a := p.a + 1, b := 2, c := p.c, d := 3, e := 4 }
```

Both records are 24 bytes; `c` is at offset 16 in `P` and at offset 12 in
`Q`, and `q.c` reads the high half of `p.b`.

### Variants

Repro [`repros/bug02b-variant-packed-layout.rr`](repros/bug02b-variant-packed-layout.rr):

```
enum M { A(u32, u64), B(u32, u32, u32) }
#[ffi(import)]
fn say(x : u64) [{ println!("{}", x) }];
fn f(m : M) -> u64 {
    match m {
        M::A(c, x) => { f(M::B{c, 1, 0}) },
        M::B(c, d, e) => { (c as u64) * 1000 + (d as u64) }
    }
}
#[main]
fn main() { say(f(M::A{5, 11})); }
```

**Command.** `rrc bug02b-variant-packed-layout.rr -O aggressive`.

**Expected.** `5001`.

**Actual on ef922049.** `11001` (`B.c` reads the low half of `A.x`), at
every `-O` level. With `--no-pack-record-members`: `5001`. `run.sh` on the
final stack (0002 and 0019 applied):

    bug 02a  FIXED       prints 7005009   [-O aggressive --no-pack-record-members]
    bug 02b  FIXED       prints 5001   [-O aggressive]

## Cause

`RcCreateFusion` runs late, after TokenReuse. It fuses `record.compound` +
`rc.create` into `rc.create_compound` (and, for variants, also
`record.variant` into `rc.create_variant`). Then it marks, in a
`skipFields` attribute, the fields whose value is a load of the same field
of the reused cell, and the lowering (`shouldSkipFieldStore` in
`BasicOpsLowering.cpp`) omits their stores.

**Structures.** `markCompoundAvoidedCopies` looks for fields to skip:

```c++
void markCompoundAvoidedCopies(ReussirRcCreateCompoundOp op) {
  auto sourceRc = op.getToken() ? getReusedRcFromToken(op.getToken())
                                : mlir::TypedValue<RcType>{};
  if (!sourceRc)
    return;
  llvm::SmallVector<int64_t> skippedFields;
  for (auto [index, field] : llvm::enumerate(op.getFields()))
    if (isLoadFromCompoundField(field, sourceRc, index))
      skippedFields.push_back(static_cast<int64_t>(index));
  ...  // set "skipFields"
}
```

`getReusedRcFromToken` follows the token back
(`token.launder(rc.reinterpret %old)`) to the old cell.
`isLoadFromCompoundField` checks that the field's value is
`ref.load(ref.project(rc.borrow %old), index)`, comparing the projection's
index with the new field's index, and nothing else: not the two record
types.

Why the types can differ: TokenReuse's `heuristic`
(`lib/Transformation/TokenReuse/TokenReuse.cpp`) reuses any token whose
size and alignment match the new cell (`sizes.haveEqualSizes`). It does
not need the same type. For `f` the IR is, in effect:

```
%old_b = reussir.rc.borrow %a                       // %a : rc<A>
%f1    = reussir.ref.load (reussir.ref.project %old_b [1])   // A.1 at offset 8
%tok   = reussir.token.launder (reussir.rc.reinterpret %a)
%b     = reussir.rc.create_compound (%c7, %f1, %c9) token(%tok)
             { skipFields = array<i64: 1> }          // B.1 at offset 4: not stored
```

This shape comes from the second `ConvertToSTD` run, which expands
TokenReuse's reuse-or-allocate step (`token.ensure`) into a
`nullable.dispatch` whose non-null arm launders `rc.reinterpret` of the
released cell and whose null arm allocates
(`ReussirTokenEnsureOpRewritePattern`), and from `RcCreateSink`, which
moves the construction into that reuse arm. That is why
`getReusedRcFromToken` can follow the token back to `%a`.

This happens under any layout, packed or not. Under the packed layout `B`
becomes `u64, u32, u32`, `B.1` sits at offset 12, and the skipped store
leaves the old cell's padding there.

**Variants.** `markVariantAvoidedCopies` → `isLoadFromVariantField` →
`hasCompatibleFieldPrefix` skip the store if, for every index 0..i, the two
arms have the same `memberIsField` flag and `structurallySameType` members,
in declaration order. That stands in for "field i is at the same offset",
which holds under the declaration-order layout only. The packed layout,
the default, sorts members by alignment, so a member's offset depends on
all the members: `A.c` is at offset 8 and `B.c` at 0. The same check uses
`structurallySameType` ([bug 4](04-recursive-type-compare.md)), which also
ignored a record's capability: a `[value]` member is stored inline and a
shared one as a pointer, so two arms could compare equal while their
layouts differ (patch 0004 compares capability and `fixed` too).

## lean2rr

**Structures:** any Lean function that consumes a structure and returns a
different structure of the same size could return a wrong field. lean2rr
cannot avoid this: the types and field orders are the program's, and
ordering fields by alignment does not make two different structures agree.
Patch 0002 fixes it.

**Variants:** lean2rr keeps its workaround (README policy: workarounds
stay, so that lean2rr also works with an unpatched Reussir), although 0019
fixes the variant half. `scripts/l2r.py` passes
`--no-pack-record-members`, and lean2rr orders each constructor's fields by
decreasing alignment itself (plan §5.1), so its records have no padding
between members, and equal member types at indices 0..i put member i at the
same offset. The prefix check is then sound.

## Patch

Two patches, one per half.

### 0002: structures

Patch file
[`patches/0002-l2r-local-bug-2-compound-skip-a-reused-struct-cell-s.patch`](patches/0002-l2r-local-bug-2-compound-skip-a-reused-struct-cell-s.patch)
(`l2r-local` commit `ae5345cf`, applied in `./reussir`; `l2r-local` head
`cc8e5aa5`). Structures only.

**The fix.** One hunk in `markCompoundAvoidedCopies`, right after the
reused cell is found:

```c++
+  // A load of the old record's field i is already in place only if the old
+  // record is laid out like the new one. Token reuse also hands a cell of
+  // one record type to another of the same size and alignment, where field
+  // i can sit elsewhere, so require the same box type.
+  if (sourceRc.getType().getInnerBoxType() !=
+      op.getRcPtr().getType().getInnerBoxType())
+    return;
```

The patch adds the test `rc_create_fusion_compound_types.mlir`: a `PA`
cell reused for a `PB` gets no `skipFields`, and a `PA` rebuilt as `PA`
keeps `skipFields = [1]`.

**Why it is correct.** MLIR types are uniqued, so equal `RcBoxType`s mean
the same record type in the same box. The two cells then have the same
layout, packed or not, and field i is at the same offset in both. The
review confirmed that `markCompoundAvoidedCopies` is the only producer of
`skipFields` on `rc.create_compound`. TRMC copies the attribute only
together with the same token.

**What it leaves unchanged.** The common case, rebuilding a structure of
the same type in its own cell (a record update), still skips the unchanged
fields. The only loss is copy avoidance between distinct structure types
that happen to have identical layouts, which is rare.

**Not covered: variants.** 0002 does not touch `markVariantAvoidedCopies`;
0019 (below) does.

**Verification.**

- Review round 1: code review as above, plus lean2rr's `StructP.lean`
  (structure updates with mixed field sizes, the `P`/`Q` conversion). The
  patched build matched native Lean; unpatched builds printed the wrong
  value. Later rounds re-ran it with every combined stack.
- On the round-2 stack: `bug02a` FIXED (`7005009`), `bug02b` still `11001`
  with the packed layout (not covered; lean2rr's flag avoids it).
- `run.sh` on the build with 0002 alone (before 0019):

      bug 02a  FIXED       prints 7005009   [-O aggressive --no-pack-record-members]
      bug 02b  REPRODUCES  prints 11001, expected 5001   [-O aggressive]

  The second line is the variant case, fixed by 0019.

**Review.** Passed in review round 1; the later rounds re-ran it in every
combined stack (rounds 2 to 4c, and round 8 with 0019 on top).

**Effect on lean2rr.** A reused structure cell always gets the fields that
sit elsewhere in the new type: the wrong-field results above are gone.

### 0019: variants

Patch file
[`patches/0019-l2r-local-bug-2-variant-skip-a-reused-variant-cell-s.patch`](patches/0019-l2r-local-bug-2-variant-skip-a-reused-variant-cell-s.patch)
(`l2r-local` commit `0218538c`, applied in `./reussir`; `l2r-local` head
`cc8e5aa5`).

**The change.** `isLoadFromVariantField` (`RcCreateFusion.cpp`) keeps the
prefix rule and, once it holds, also requires field i to sit at the same
byte offset from the box in the old and the new cell
(`sameVariantFieldOffset`):

```c++
-  return borrow && borrow.getRcPtr() == sourceRc;
+  if (!borrow || borrow.getRcPtr() != sourceRc)
+    return false;
+  return sameVariantFieldOffset(sourceRc.getType(), targetRc.getType(),
+                                sourcePayloadType, targetPayloadRecord,
+                                fieldIndex, dataLayout);
```

The offset is the sum of three parts, each compared:

- where the element starts in the box: the same box header shape
  (`isHeaderFused`, `getHeaderTypes`) and the same element alignment;
- where the arm payload starts in the variant (`getVariantPayloadOffset`):
  after the header (the fused 8-byte count-and-tag word, or the bare tag),
  at the alignment of the most aligned arm, as `getTypeSizeInBits` lays the
  variant out;
- where member i sits in the payload: the new
  `RecordType::getMemberOffset` (`lib/IR/ReussirTypes.cpp`), the packed
  member offsets from the same derivation the type sizes already use
  (`getElementRegionLayoutInfo` now shares it through
  `derivePhysicalCompoundLayout`), which the type converter's LLVM structs
  follow.

`markVariantAvoidedCopies` gets the module's data layout for this. In the
repro, `A.0` is at payload offset 8 and `B.0` at 0, so the store of `B.c`
is no longer skipped.

**Why it is correct.** The check only removes skips: a field whose store
is still skipped satisfies the old prefix rule and sits at the same byte
offset in both cells, so the bytes the new arm reads are the ones the load
read. Reusing a cell for the same arm, arms of the same variant under
`--no-pack-record-members`, and cells of another variant whose payload and
member offsets agree skip as before (the test checks both directions).
The offsets come from the derivation that also gives LLVM its struct
layout, so they are the offsets the stores and loads use.

**Verification.**

- Test `tests/integration/conversion/rc_create_fusion_variant_layout.mlir`:
  the repro's shape gets no `skipFields` under the packed layout; agreeing
  offsets keep theirs.
- lean2rr's code is the same with and without the patch (identical LLVM IR
  for the classic corpus and a sample of the runtime tests): it uses
  `--no-pack-record-members`, where the prefix rule was already sound.
- `run.sh` on the final stack: `bug 02b  FIXED       prints 5001   [-O aggressive]`.

**Review.** Round 8 (local review notes):
no correctness defect. Checked: `getVariantPayloadOffset` is the header
formula of `getTypeSizeInBits` and the offset LLVM gives the payload
member; `getMemberOffset` and `deriveCompoundLayout` use
`memberStorageType`, which agrees with the type converter's
`getProjectedType` for every member kind (records, rc, `Nullable`,
closures, arrays, cells); equal header types plus equal element alignment
give an equal element offset, regional boxes included; cross-variant reuse
with a different region alignment (8 against 16) never skips; recursive
members are pointers and `structurallySameType` is coinductive (0004); the
new tag store never overlaps a payload field; with 0023 (cell glue) it
shares no logic. Repro 02b is FIXED.

**Effect on lean2rr.** None today (it passes `--no-pack-record-members` and
keeps doing so). Reussir's default packed layout becomes safe for variants;
lean2rr orders its fields by alignment itself, so the flag costs it
little.

## Upstream note

`markCompoundAvoidedCopies` (RcCreateFusion) skips the store of field i of
a struct built in a reused cell whenever the value is a load of field i of
the old cell, comparing only the index. Token reuse also gives a cell of
one struct type to another of the same size, where field i can sit at
another offset. Repro: `struct A(u64, u32)` consumed into
`struct B(u32, u32, u64)` as `B{7, a.1, 9}` reads `B.1 = 0`. Requiring the
same box type fixes it. The variant path (`hasCompatibleFieldPrefix`) has
the same problem under the packed layout (`enum M { A(u32, u64), B(u32,
u32, u32) }`: `M::B` built in a reused `M::A` cell reads `B.0` from `A.1`);
requiring field i to sit at the same byte offset from the box (element,
payload and member offsets) fixes that half.
