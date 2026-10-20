# 18. A returned struct with tail padding comes back in memory

**Kind:** missed optimization. Not a bug: rrc's output is correct.

## Summary

**Kind:** missed optimization. **Status:** worked around: the tuple of a
`flatten-structs` result, the struct that lean2rr returns, keeps a `bool`,
`u8`, `u16` or `u32` in a whole `u64` member and has no member for a unit
value, so it has no tail padding (`tupleMemberTy` in
`lean2rr/LeanToReussir/LowerBase.lean`). Not patched. It shows with and
without `--no-pack-record-members`: with Reussir's packed order the
narrow members come last, so the padding is at the end.

**Upstream (2026-10-20):** Found on upstream 7954a367 with the series
(`l2r-base3`); not reported upstream.

## Repro

[`repros/bug18-tail-padding-return.rr`](repros/bug18-tail-padding-return.rr),
`reussir-bugs/repros/run.sh RRC_CHECKOUT 18`:

```rust
pub struct [value] T1(u64, bool)
pub struct [value] T2(u64, u64)

pub fn f1(n : u64, b : bool) -> T1 { T1{n + 1, b} }
pub fn f2(n : u64, b : u64) -> T2 { T2{n + 1, b} }
```

With `rrc --emit asm -O aggressive` (with or without
`--no-pack-record-members`), on aarch64:

- `f1` stores its result through `x8` (`str x9, [x8]`, `strb w1, [x8,
  #8]`): the caller passes the address of a stack slot and reads the
  result back from memory.
- `f2` returns in `x0` and `x1` (one `add`).

## Cause

`lib/Conversion/TypeConverter/TypeConverter.cpp`, the conversion of a
compound record to an LLVM struct: when the members end before the
record's size (`currentSize < expectedTotalSize`), the conversion appends
the rest as an explicit byte array, `T1` = `{ i64, i1, [7 x i8] }`. An
LLVM struct is padded to its alignment by itself (`{ i64, i1 }` is 16
bytes too), so here the array changes no size and no offset. But a struct
returned by value is split into its values, and each element of the array
is one more value: `T1` has 9. AArch64's return convention has 8
registers, so LLVM returns a struct of more than 8 values in memory
(`sret` demotion), whatever the convention of the function (`fastcc`
too). A copy of such a struct copies the padding bytes as well. LLVM's
dead-argument elimination removes unread elements of an internal
function's result, so the cost stays only where the whole struct is used:
a result that a recursive call returns again as it is, a struct stored
whole.

Possible fixes in Reussir (not made): append the byte array only when
LLVM's own padding of the members (`alignTo(currentSize, largest member
alignment)`) is smaller than the record's size; or make the tail padding
part of the last member, as the conversion does for padding between
members (but see [entry 17](17-padded-member-widening.md)).

## What lean2rr does

- The tuple of a `flatten-structs` result (`L2RFlat.Tuple<k>`, lowered by
  `tupleType` with `flat`) keeps a `bool`, `u8`, `u16` or `u32` value in
  a `u64` member (a `bool` as 1 or 0, the others zero-extended;
  `toTupleMember`, `ofTupleMember`) and has no member for a unit value
  (`L2RUnit`, one byte), unless all its values are units. Its members are
  then words and pointers (or types lean2rr does not widen: `f32`,
  enumerations, `[value]` structs of narrow fields), so it has no tail
  padding.
- Found in timing run 8 (dev b141a3a5): dev b874c365 sorted every
  generated tuple by decreasing alignment ([entry 17](17-padded-member-widening.md)),
  so the tag of a flattened `Option` or `Except` (a `bool`) came last.
  Unionfind's `findEntryAux` returns `(String, nodeData, Array, bool)`,
  `{ ptr, ptr, ptr, i1, [7 x i8] }`, and returns its own recursive call's
  result as it is: it returned in memory and ran 16% more instructions;
  the program's median wall time went from 448 to 477 ms (runs 7 and 8).
  Call sites that pass a stack slot in `x8` to a program function, in
  the binaries of runs 7 and 8: Unionfind 0 → 5, MonadicInterp 22 → 26,
  Liasolver 0 → 2, Zip (Z03) 21 → 43, Cedar (Z06) 20 → 41.
- With whole-word members and no unit members (cachegrind, SVE-free
  builds, the benchmark arguments, dev b874c365 → the change): Unionfind
  (n = 3000000) 9.397 → 8.256 billion instructions (−12.1%),
  MonadicInterp (n = 30000) 21.758 → 20.351 billion (−6.5%); no program
  function of Unionfind, MonadicInterp, Liasolver, Strings or ExprEval is
  returned in memory any more.
- A join point's tuple (J2) is not returned and keeps its values' own
  types: there the padding at the end costs nothing.
