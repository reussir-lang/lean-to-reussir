/-! Runtime test: `ByteArray.data` and `ByteArray.mk` (to and from
`Array UInt8`), `FloatArray.data` and `FloatArray.mk` (to and from
`Array Float`): leanrt's one-loop conversions at the exact size
(`leanrt::array::boxes_of_bytes`, ...), at sizes around the block
boundaries, of a source that is shared or used again afterwards, of arrays
built by pushes and by `map`, every byte value, and floats that are NaN,
infinite, negative zero or big. The program has no `unsafeCast`, so the
conversions are the textures alone (`RtByteArrayDataCast` has the casting
shape). -/

def mix (h x : UInt64) : UInt64 := (h ^^^ x) * 1099511628211

@[noinline] def mkBytes (n : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity n
  for i in [0:n] do b := b.push (i * 37 + 11).toUInt8
  return b

@[noinline] def digA (a : Array UInt8) : UInt64 := a.foldl (fun h x => mix h x.toUInt64) 7
@[noinline] def digB (b : ByteArray) : UInt64 := b.foldl (fun h x => mix h x.toUInt64) 7
@[noinline] def digF (a : Array Float) : UInt64 := a.foldl (fun h x => mix h x.toBits) 7
@[noinline] def digFA (a : FloatArray) : UInt64 := a.foldl (fun h x => mix h x.toBits) 7

@[noinline] def floats (n : Nat) : Array Float :=
  (Array.range n).map fun i => i.toFloat * 1.5 - 7.25

def main : IO Unit := do
  for n in [0, 1, 2, 7, 8, 9, 15, 16, 17, 255, 256, 1000, 4096, 100003] do
    let b := mkBytes n
    let d := b.data
    let b2 := ByteArray.mk d
    -- `b` is used again after `data`: the source is shared.
    IO.println s!"bytes {n}: {d.size} {digA d} {b2.size} {digB b2} {b2 == b} {digB b}"
  -- Every byte value, through `data` and back, and `mk` of a pushed array.
  let all : Array UInt8 := (Array.range 256).map (·.toUInt8)
  let ba := ByteArray.mk all
  IO.println s!"all {ba.size} {ba.data == all} {digA ba.data} {(ByteArray.mk ba.data).toList.take 5}"
  let mut pushed : Array UInt8 := #[]
  for i in [0:3000] do pushed := pushed.push (i % 251).toUInt8
  IO.println s!"pushed {(ByteArray.mk pushed).size} {digB (ByteArray.mk pushed)} {digA pushed}"
  -- `data` of a unique byte array (the last use).
  IO.println s!"unique {digA (mkBytes 5000).data}"
  -- Floats.
  for n in [0, 1, 3, 8, 1000] do
    let a := floats n
    let fa := FloatArray.mk a
    let back := fa.data
    IO.println s!"floats {n}: {fa.size} {digFA fa} {back.size} {digF back} {digF a}"
  let special : Array Float := #[0.0, -0.0, 1.0 / 0.0, -1.0 / 0.0, 0.0 / 0.0, 1e300, 5e-324, 2.0 ^ 63, 18446744073709551615.0]
  let fs := FloatArray.mk special
  IO.println s!"special {fs.size} {digFA fs} {fs.data.map (·.toBits) |>.toList}"
  IO.println s!"special back {(FloatArray.mk fs.data).toList.map (·.toBits)}"
