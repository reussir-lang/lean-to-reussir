# Patch 0002: a reused structure cell keeps a stale field (bug 2, structures)

Patch file: `../0002-l2r-local-bug-2-compound-skip-a-reused-struct-cell-s-field-store.patch`
(`l2r-local` commit `f80e1f65`). Bug section:
[docs/reussir-bugs.md, bug 2](../../docs/reussir-bugs.md#2-in-place-reuse-skips-stores-of-fields-that-sit-elsewhere-in-the-new-record).

## 1. Summary

When a function consumes a structure and builds another of the same size,
Reussir writes the new structure into the old cell (token reuse). It then
skips the store of any field i whose new value was just read from field i
of the old cell, assuming the bytes are already there. It compared only
the field *index*, not the two types. In a different structure type,
field i can sit at a different offset, so the new structure kept whatever
bytes the old one had at that offset: a wrong value with no error. The
patch skips such stores only when the old and new cells have the same
type. The same mistake for enum variants under Reussir's default packed
layout is not patched. lean2rr avoids it with a flag.

## 2. Symptom

Repro `docs/reussir-bugs/bug02a-struct-reuse.rr`:

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

Command: `rrc bug02a-struct-reuse.rr -O aggressive --no-pack-record-members`.

- Expected: `7005009`, that is `B{7, 5, 9}`.
- Actual on ef922049: `7000009` at every `-O` level, with and without
  `--reuse-across-call` and `--no-pack-record-members`. `run.sh` printed
  `bug 02a  REPRODUCES  prints 7000009, expected 7005009   [-O aggressive --no-pack-record-members]`.

With declaration-order layout, `A` has `u64` at payload offset 0 and `u32`
at 8. `B` has `u32` at 0, `u32` at 4 and `u64` at 8. Both are 16-byte
payloads, so `f`'s `B` reuses `a`'s cell. `B.1 = a.1` is a load of field 1
of the old cell, so its store is skipped. `B.1` then reads bytes 4..8 of
the old payload, the high half of `A.0 = 123`, which is 0. In Lean terms, with
lean2rr's field order (docs/reussir-bugs.md):

```lean
structure P where a : UInt64; b : UInt64; c : UInt32
structure Q where a : UInt64; b : UInt32; c : UInt32; d : UInt32; e : UInt32
@[noinline] def conv (p : P) : Q := { a := p.a + 1, b := 2, c := p.c, d := 3, e := 4 }
```

Both are 24 bytes. `c` is at offset 16 in `P` and 12 in `Q`, so `q.c` reads
the high half of `p.b`.

## 3. Root cause

`RcCreateFusion` (`lib/Transformation/RcCreateFusion/RcCreateFusion.cpp`)
runs late, after TokenReuse. It fuses `record.compound` + `rc.create` into
`rc.create_compound`. Then `markCompoundAvoidedCopies` looks for fields to
skip:

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
index with the new field's index, and nothing else. The lowering
(`shouldSkipFieldStore` in `BasicOpsLowering.cpp`) then omits the store.

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

This happens under any layout, packed or not. Under the packed layout `B`
becomes `u64, u32, u32`, `B.1` sits at offset 12, and the skipped store
leaves the old cell's padding there.

The variant version of the check (`markVariantAvoidedCopies` →
`hasCompatibleFieldPrefix`) at least compares the member types at indices
0..i. That implies equal offsets under declaration order but not under
the default packed layout, which sorts members by alignment. That is the
unpatched variant half of bug 2 (`bug02b-variant-packed-layout.rr`).

## 4. The fix

One hunk in `markCompoundAvoidedCopies`, right after the reused cell is
found:

```c++
+  // A load of the old record's field i is already in place only if the old
+  // record is laid out like the new one. Token reuse also hands a cell of
+  // one record type to another of the same size and alignment, where field
+  // i can sit elsewhere, so require the same box type.
+  if (sourceRc.getType().getInnerBoxType() !=
+      op.getRcPtr().getType().getInnerBoxType())
+    return;
```

**Why it is correct.** MLIR types are uniqued, so equal `RcBoxType`s mean
the same record type in the same box. The two cells then have the same
layout, packed or not, and field i is at the same offset in both. The
review confirmed that `markCompoundAvoidedCopies` is the only producer of
`skipFields` on `rc.create_compound`. TRMC copies the attribute only
together with the same token.

**What it leaves unchanged.** The common case, rebuilding a structure of
the same type in its own cell (a record update), still skips the
unchanged fields. The only loss is copy avoidance between distinct
structure types that happen to have identical layouts, which is rare.

**Not covered: variants.** The patch does not touch
`markVariantAvoidedCopies`. lean2rr avoids that case another way (section
6), so no variant patch was adopted.

The patch adds `rc_create_fusion_compound_types.mlir`: a `PA` cell reused
for a `PB` gets no `skipFields`, and a `PA` rebuilt as `PA` keeps
`skipFields = [1]`.

## 5. Verification

- Review round 1: code review as above, plus lean2rr's `StructP.lean`
  (structure updates with mixed field sizes, the `P`/`Q` conversion). The
  patched build matched native Lean. Unpatched builds printed the wrong
  value. Later rounds re-ran it with every combined stack.
- `run.sh` on the patched build:

      bug 02a  FIXED       prints 7005009   [-O aggressive --no-pack-record-members]
      bug 02b  REPRODUCES  prints 11001, expected 5001   [-O aggressive]

  The second line is the unpatched variant case, under the packed layout
  that lean2rr does not use. With `--no-pack-record-members` it prints
  `5001`.

## 6. Effect on lean2rr

Any Lean function that consumes a structure and returns a different
structure of the same size could return a wrong field. lean2rr cannot
avoid this: the types and field orders are the program's, and ordering
fields by alignment does not make two different structures agree. The
patch fixes it.

For variants, lean2rr keeps its workaround. `scripts/l2r.py` passes
`--no-pack-record-members`, and lean2rr orders each constructor's fields
by decreasing alignment itself (plan §5.1). So its records have no padding
between members, and equal member types at indices 0..i put member i at
the same offset. The prefix check is then sound.

## 7. Upstream note

`markCompoundAvoidedCopies` (RcCreateFusion) skips the store of field i of
a struct built in a reused cell whenever the value is a load of field i of
the old cell, comparing only the index. Token reuse also gives a cell of
one struct type to another of the same size, where field i can sit at
another offset. Repro: `struct A(u64, u32)` consumed into
`struct B(u32, u32, u64)` as `B{7, a.1, 9}` reads `B.1 = 0`. Requiring the
same box type fixes it. The variant path (`hasCompatibleFieldPrefix`) has
the same problem under the packed layout.
