# Patch 0004: equal recursive types crash rrc (bug 4)

Patch file: `../0004-l2r-local-bug-4-compare-recursive-record-types-coind.patch`
(`l2r-local` commit `9736cfe5`). Bug section:
[docs/reussir-bugs.md, bug 4](../../docs/reussir-bugs.md#4-structurallysametype-recurses-forever-on-equal-recursive-types).

## 1. Summary

When a construction reuses the cell of a value that was just freed,
Reussir tries to skip storing fields whose bytes are already in place
("copy avoidance"). To decide that, it compares the old and new record
types member by member. The comparison follows member records with no
memory of what it is already comparing. Two distinct recursive types with
the same shape, such as a user's `MyList` and `List`, made it recurse
until rrc's worker thread ran out of stack: rrc died with SIGSEGV and no
message. The patch compares coinductively: a pair of types met again while
it is still being compared counts as equal. The patch also compares each
record's capability (`[value]` or shared) and `fixed` flag. Without those
two checks, fixing the crash would have turned some of these programs into
silent miscompiles.

## 2. Symptom

Repro `docs/reussir-bugs/bug04-recursive-type-compare.rr`:

```
enum L1 { Cons(u64, L1), Nil }
enum L2 { Cons(u64, L2), Nil }
enum [value] V { C(u64, L1), N }
enum [value] W { C(u64, L2), N }
enum S1 { A(V, u64), Z }
enum S2 { A(W, u64), Z }
#[ffi(import)]
fn say(x : u64) [{ println!("{}", x) }];
#[ffi(import)]
fn num() -> u64 [{ 1005 }];
fn conv(s : S1) -> S2 {
    match s { S1::A(c, v) => { S2::A{W::N{}, v} }, S1::Z => { S2::Z{} } }
}
fn get(s : S2) -> u64 { match s { S2::A(d, v) => { v }, S2::Z => { 0 } } }
#[main]
fn main() { say(get(conv(S1::A{V::C{1, L1::Nil{}}, num()}))); }
```

Command: `rrc bug04-recursive-type-compare.rr -O aggressive`.

- Expected: compiles; prints `1005`.
- Actual on ef922049: rrc dies with SIGSEGV (exit 139), no message, at
  every `-O` level. `run.sh` printed
  `bug 04   REPRODUCES  rrc killed by SIGSEGV   [-O aggressive]`.

In lean2rr this appeared as a user `MyList` next to `List`, with
`MyList.toList` reusing cons cells under `--reuse-across-call`.

## 3. Root cause

**Copy avoidance.** Token reuse lets a construction write into a freed cell
of the same size. After that, `RcCreateFusion`
(`lib/Transformation/RcCreateFusion/RcCreateFusion.cpp`) fuses
`record.compound` + `record.variant` + `rc.create` into
`rc.create_variant` and marks, in a `skipFields` attribute, the fields
whose value is a load of the same field of the reused cell. The LLVM
lowering then skips their stores (`shouldSkipFieldStore` in
`BasicOpsLowering.cpp`). For variants the test is
`markVariantAvoidedCopies` → `isLoadFromVariantField` →
`hasCompatibleFieldPrefix`. Field i may be skipped if, for every index 0..i,
the two arms have the same `memberIsField` flag and
`structurallySameType` members. That check stands in for "field i is at
the same offset". It is only valid under the declaration-order layout,
which is the variant half of bug 2 (0002.md).

**The comparison** on ef922049:

```c++
bool structurallySameType(mlir::Type lhs, mlir::Type rhs) {
  if (lhs == rhs)
    return true;
  auto lhsRecord = llvm::dyn_cast<RecordType>(lhs);
  auto rhsRecord = llvm::dyn_cast<RecordType>(rhs);
  if (lhsRecord || rhsRecord) {
    if (!lhsRecord || !rhsRecord)
      return false;
    if (lhsRecord.isVariant() != rhsRecord.isVariant()) return false;
    if (lhsRecord.isCompound() != rhsRecord.isCompound()) return false;
    if (lhsRecord.getComplete() != rhsRecord.getComplete()) return false;
    if (lhsRecord.getMembers().size() != rhsRecord.getMembers().size())
      return false;
    for (... each member pair ...) {
      if (lhsField != rhsField) return false;
      if (!structurallySameType(lhsMember, rhsMember)) return false;
    }
    return true;
  }
  return false;
}
```

Named records in the Reussir dialect are uniqued by name, so a recursive
member such as `L1` inside `L1::Cons` is the complete `L1` type again.
`lhs == rhs` stops the recursion only when both sides are the very same
type. In the repro, `conv` reuses the `S1` cell for an `S2`, and `v` (field
1) is a load of `S1::A`'s field 1, so fields 0..1 are compared:

```
S1::A.0 = V   vs  S2::A.0 = W
  V::C = (u64, L1)  vs  W::C = (u64, L2)
    L1  vs  L2
      L1::Cons = (u64, L1)  vs  L2::Cons = (u64, L2)
        L1  vs  L2          ... forever
```

The pass runs on an MLIR/LLVM worker thread with a fixed stack, so the
overflow is a SIGSEGV whatever `ulimit -s` says.

**A second hole, found in review.** Even when it terminates, the
comparison ignores a record's default capability. A `[value]` record
member is stored inline. A shared one is stored as an 8-byte pointer. So
two records with the same members can occupy different sizes as members,
and the following field sits at different offsets. Review round 1 found
it twice:

- RV-4, without recursion, already wrong on ef922049:
  `enum [value] C { R(u64, u64), B }` against `enum D { R(u64, u64), B }`,
  with `S1 { A(C, u64) }` reused for `S2 { A(D, u64, u64, u64) }`. The
  store of `S2::A.1` is skipped. Expected `100579`, prints `579`.
- RV-1, the same with recursive members: ef922049 crashes, and the
  coinductive fix alone turned the crash into the same silent
  miscompile.

## 4. The fix

All changes are in `structurallySameType` and a new wrapper.

```c++
using AssumedEqualTypes = llvm::DenseSet<std::pair<mlir::Type, mlir::Type>>;

bool structurallySameType(mlir::Type lhs, mlir::Type rhs,
                          AssumedEqualTypes &assumed) {
  if (lhs == rhs)
    return true;
  ...
    if (!lhsRecord || !rhsRecord)
      return false;
+   if (!assumed.insert({lhs, rhs}).second)
+     return true;
    if (lhsRecord.isVariant() != rhsRecord.isVariant())
      return false;
+   if (lhsRecord.getDefaultCapability() != rhsRecord.getDefaultCapability())
+     return false;
+   if (lhsRecord.getFixed() != rhsRecord.getFixed())
+     return false;
    ...
-     if (!structurallySameType(lhsMember, rhsMember))
+     if (!structurallySameType(lhsMember, rhsMember, assumed))
  ...
}

bool structurallySameType(mlir::Type lhs, mlir::Type rhs) {
  AssumedEqualTypes assumed;
  return structurallySameType(lhs, rhs, assumed);
}
```

- **Coinduction.** When a pair of record types is met again, it is assumed
  equal. Any mismatch anywhere below makes every caller return `false`
  immediately, up to the top. So the assumption can only "close" a cycle
  whose members all match. That is the standard bisimulation argument for
  equality of recursive types. Pairs stay in the set after their
  comparison finishes. This is harmless: a pair that finished `true` is
  equal under the assumptions, and one that finished `false` made the
  whole answer `false`. Each top-level call gets a fresh set, and there
  are finitely many type pairs, so the comparison terminates. Inputs
  without recursion give the old answer, apart from the two new checks.
- **Capability and `fixed`.** The default capability decides how a member
  of the type is stored (inline or as a pointer). Per the patch comment,
  `fixed` decides how a variant box is sized. Records that differ in
  either only look alike.
- Callers are unchanged. After 0002 only the variant prefix check uses the
  function.

The patch adds `rc_create_fusion_recursive_types.mlir`. A `MyList` cons
cell reused for a `List` cons gets `skipFields = [1]`, which is correct:
the head keeps its place. An "Other" list whose `Nil` arm differs gets no
skip. A `[value]` record against a shared one of the same shape (the RV-1
layout) gets no skip.

## 5. Verification

- Review round 1 checked the coinductive rule itself and found it sound
  for the attributes it compares. It found RV-1 and RV-4 (above), which
  led to the capability and `fixed` checks.
- Round 2: RV-1 and RV-4 both print `100579`, in plain and ASan builds. A
  deep mutual recursion with a capability difference two levels down is
  correct with and without packing, at `-O none` and `aggressive`
  (unpatched rrc crashes). The reviewer's argument for why these
  attributes are enough: a member's storage is fully determined by
  `isField`, the record's default capability, and type identity for
  non-records. Record members can only carry `field`/unspecified
  capability. No surface type is more than 8-aligned, so variant payload
  offsets coincide whenever a token fits.
- Differential fuzzing in every round, and lean2rr's `MyListP` (user list
  ↔ `List`, rose trees, pair swaps) against native Lean.
- `run.sh` on the patched build:
  `bug 04   FIXED       compiles, prints 1005   [-O aggressive]`.

## 6. Effect on lean2rr

Programs with a user type of the same shape as another recursive type,
converting one into the other (`MyList.toList`, a copy of `List`, `Option`
look-alikes), no longer crash rrc.

`scripts/l2r.py` still retries rrc without `--reuse-across-call` when rrc
dies from a signal. Its comment still names this bug. The retry is now
only a fallback for unknown crashes; it never helped when the crash also
happened without the flag, as in this repro. This patch does not change
the variant half of bug 2: the prefix check still assumes declaration
order. lean2rr keeps `--no-pack-record-members` for that.

## 7. Upstream note

`RcCreateFusion`'s `structurallySameType` recurses without a visited set,
so two distinct recursive record types of the same shape (e.g. a user list
and a library list, when a cell of one is reused for the other) overflow
the pass thread's stack (rrc SIGSEGV). It also ignores a record's default
capability, so a `[value]` member (inline) and a shared one (pointer) can
compare equal and a field store is wrongly skipped, even without
recursion. Suggested fix: coinductive comparison with a set of assumed
pairs, plus comparing `defaultCapability` and `fixed`.
