# 17. A member widened over its padding is stored at its own width

**Kind:** missed optimization. Not a bug: rrc's output is correct.

## Summary

**Kind:** missed optimization. **Status:** worked around: lean2rr puts
the fields of every tuple it generates (join-point tuples,
`flatten-structs` results) in decreasing alignment (`memberOrder`), as it
already does for records (`field-order`), so no member has padding after
it. Not patched. It shows only with
`--no-pack-record-members`, which lean2rr's driver passes; Reussir's
default packed order has no padding between members.

**Upstream (2026-10-19):** Found on upstream 7954a367 with the series
(`l2r-base3`); not reported upstream.

## Repro

[`repros/bug17-padded-member-widening.rr`](repros/bug17-padded-member-widening.rr),
`reussir-bugs/repros/run.sh RRC_CHECKOUT 17`:

```rust
struct [value] TBN(bool, u64)
struct [value] TNB(u64, bool)

pub fn f_bn(c : u32, n : u64) -> u64 {
    let jv : TBN = {
        if c > 96 { TBN{c < 123, n} } else { TBN{false, n} }
    };
    let b : bool = jv.0;
    let m : u64 = jv.1;
    if b { m + 1 } else { m }
}
```

`f_nb` is the same with the fields in the other order. With
`rrc --emit llvm-ir -O aggressive --no-pack-record-members`:

- `f_bn` keeps two `alloca i8`: each arm stores its `bool` (`store i1`),
  loads it back as `i8` and masks it (`and i8 %x, 1`) after the join.
- `f_nb` is four instructions: `add i32 %c, -97`, `icmp ult`, `zext`,
  `add`.

## Cause

`lib/Conversion/TypeConverter/TypeConverter.cpp`, the conversion of a
record to an LLVM struct: when the next member needs alignment padding,
the previous member is lifted to an integer that covers the padding
("Widen the previous member over the padding only to an integer no more
aligned than the next member"; upstream #658, commit `e8e85b40`, in the
base, limited the widening to that integer). `TBN` becomes `{ i64, i64 }`, while `TNB`
keeps its `bool` as `{ i64, i1, [7 x i8] }`. The lowering of a field store
still writes the field's own type into the widened member (`store i1` at
offset 0), and the struct value is then loaded whole (`load %TBN`): 63 bits
of the first `i64` were never written. LLVM's SROA cannot rewrite that load
from the store, so the slot stays in memory, and the conditions that depend
on the `bool` are no longer folded into the code around them.

Possible fixes in Reussir (not made): explicit padding after the member
(`{ i1, [7 x i8], i64 }`), as the conversion does when no integer fits; or
a store of the field zero-extended to the widened integer.

## What lean2rr does

- Records: their fields are already in decreasing alignment
  (`Opt/FieldOrder.lean`, `field-order`), so no member is padded.
- Join-point tuples (J2, `LowerBase.lean`: `tupleType`, `memberOrder`):
  the same order since the fix of the run-7 regressions. Before it, the tuple followed
  the join point's parameter order. The parameter order by first use
  (`stableJpParams`, dev 713037fa) made the tuple of `'a' ≤ c && c ≤ 'z'`
  in Strings' `charStats` loop `(bool, Nat)` instead of `(Nat, bool)`, and
  the program ran 3.0% more instructions (cachegrind, 13.97 → 14.39
  billion; `docs/implementation/control-flow/join-points.md`).
- The tuples of `flatten-structs` (`L2RFlat.Tuple<k>`, the same
  `tupleType` and `memberOrder`): the same order since the change that
  follows the fix of the run-7 regressions. Before it, they kept the
  order of the structure's fields; an `Option` result is flattened to
  `(bool, value)`, for example Strings' `String.Slice.toNat?` returned
  `Tuple(bool, Nat)`, now `Tuple(Nat, bool)`. Across run 7's programs,
  1144 of 1999 tuple types had a smaller field before a larger one, in 38
  programs.
- `--no-pack-record-members` itself was a workaround for a Reussir bug
  that upstream fixed (#652, #656;
  `docs/implementation/reussir-workarounds/correctness-bugs.md`, old
  bug 2). Without the flag, Reussir packs every record and this issue
  cannot occur.
