# 8. A padding "lift" breaks declaration-order layouts

## Summary

**Kind:** bug. **Status:** does not affect lean2rr (it never emits the
shape). No patch yet.

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
(packed) layout it prints `2550200000`.

## Cause

`lib/Conversion/TypeConverter/TypeConverter.cpp`, `convertRecordType`:
under `--no-pack-record-members`, a member followed by padding is widened
to an integer that covers the padding, without checking that this integer
is no more aligned than the next member. Reussir's layout of `Q` is 6
bytes with alignment 2; its LLVM type `{ i32, i16 }` is 8 bytes with
alignment 4. Reussir allocates `R` as 38 bytes, LLVM's `R` is 52, so every
list cell is written past its end. Reussir's and LLVM's field offsets also
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
