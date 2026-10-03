# 1. `[value]` enum payloads lost in the LLVM lowering

## Summary

**Kind:** bug. **Status:** worked around (lean2rr emits only unaffected
`[value]` enums). No patch yet.

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
pointer can lose its upper bytes (SIGSEGV).

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
