/-! Runtime test (review of the runtime's speed items): boxed `Float` and
big `UInt64` cells (from 2^63; leanrt's scalar cells, read in line): shared
and last-reference reads, copy-on-write of arrays holding cells,
`FloatArray`/`ByteArray` conversions of shared and unique sources (the
one-loop `ByteArray.mk`, `.data` and their `FloatArray` twins), special
floats, the same cell many times. -/

@[noinline] def bigs (n : Nat) : Array UInt64 := Id.run do
  let mut a := #[]
  for i in [0:n] do a := a.push (((1 : UInt64) <<< 63) + i.toUInt64 * 3)
  a

@[noinline] def floats (n : Nat) : Array Float := Id.run do
  let mut a := #[]
  for i in [0:n] do a := a.push (i.toFloat * 0.5 - 3.25)
  a

@[noinline] def specials : Array Float :=
  #[Float.ofBits 0x7ff0000000000123, Float.ofBits 0xfff8000000000abc, -0.0, 0.0,
    Float.ofBits 0x7ff0000000000000, Float.ofBits 0x0000000000000001, Float.ofBits 0x7ff4000000000000]

@[noinline] def sumU (a : Array UInt64) : UInt64 := a.foldl (· + ·) 0
@[noinline] def sumBits (a : Array Float) : UInt64 := a.foldl (fun s x => s * 31 + x.toBits) 0
@[noinline] def sumFA (a : FloatArray) : UInt64 := a.foldl (fun s x => s * 31 + x.toBits) 0
@[noinline] def sumBA (a : ByteArray) : Nat := a.foldl (fun s x => s * 7 + x.toNat) 0 % 1000000007

@[noinline] def keep {α} (x : α) : IO α := pure x

def main (args : List String) : IO Unit := do
  let n := args.head!.toNat!
  let mut acc : UInt64 := 0
  for round in [0:3] do
    -- copy-on-write of an Array UInt64 of cells, both versions read
    let a := bigs (n + round)
    let b := a.set! 0 7
    let c := a.set! 1 ((1 : UInt64) <<< 63)
    acc := acc + sumU a + sumU b * 3 + sumU c * 5
    -- a read by index while shared, then the last reference
    let a2 ← keep a
    acc := acc + a2[2]! + a2[n / 2]!
    -- Float arrays
    let f := floats (n + round)
    let g := f.set! 0 1.0
    acc := acc + sumBits f + sumBits g * 3
    -- FloatArray.mk of a shared and a unique source
    let fa := FloatArray.mk f
    acc := acc + sumFA fa + sumBits f
    let fa2 := FloatArray.mk (floats (n + round))
    acc := acc + sumFA fa2
    -- FloatArray.data, round trip, and the original kept
    let fd := fa.data
    acc := acc + sumBits fd + sumFA fa
    let fd2 := (FloatArray.mk specials).data
    acc := acc + sumBits fd2 + sumBits specials
    IO.println s!"specials {fd2.map Float.toBits}"
    -- the same cell many times
    let r := Array.replicate (n + round) (Float.ofBits 0x7ff00000000000ff)
    let r2 := Array.replicate (n + round) (((1 : UInt64) <<< 63) + 5)
    acc := acc + sumBits r + sumFA (FloatArray.mk r) + sumU r2 + sumU (r2.set! 0 1)
    -- ByteArray
    let bs : Array UInt8 := (List.range (n + round)).toArray.map (·.toUInt8)
    let ba := ByteArray.mk bs
    let ba2 := ByteArray.mk (bs.set! 0 9)
    acc := acc + (sumBA ba + sumBA ba2 + bs.size).toUInt64
    let bd := ba.data
    acc := acc + (sumBA ba + bd.foldl (fun s x => s + x.toNat) 0).toUInt64
    let e := ByteArray.mk #[]
    let ed := ByteArray.empty.data
    let fe := FloatArray.mk #[]
    acc := acc + e.size.toUInt64 + ed.size.toUInt64 + fe.size.toUInt64 + FloatArray.empty.data.size.toUInt64
  IO.println s!"acc {acc}"
