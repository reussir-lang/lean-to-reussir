/-! Runtime test (review of the runtime's speed items): `ByteArray.mk` and
`FloatArray.mk` in a program that casts (`unsafeCast`): arrays of other word
types read as `UInt8` or `Float`, through the checked conversion textures
or the generated loop. -/

def mix (h x : UInt64) : UInt64 := (h ^^^ x) * 1099511628211
@[noinline] def digB (b : ByteArray) : UInt64 := b.foldl (fun h x => mix h x.toUInt64) 7
@[noinline] def digFA (a : FloatArray) : UInt64 := a.foldl (fun h x => mix h x.toBits) 7

@[noinline] unsafe def u64AsFloats (a : Array UInt64) : Array Float := unsafeCast a
@[noinline] unsafe def floatsAsU64 (a : Array Float) : Array UInt64 := unsafeCast a
@[noinline] unsafe def u32AsBytes (a : Array UInt32) : Array UInt8 := unsafeCast a
@[noinline] unsafe def charsAsBytes (a : Array Char) : Array UInt8 := unsafeCast a
@[noinline] unsafe def boolsAsBytes (a : Array Bool) : Array UInt8 := unsafeCast a
@[noinline] unsafe def u16AsBytes (a : Array UInt16) : Array UInt8 := unsafeCast a

unsafe def main : IO Unit := do
  let u : Array UInt64 := #[0, 1, 0x3ff0000000000000, 0x7ff0000000000123, 0x8000000000000000, 0xfff8000000000001, 0xffffffffffffffff]
  let f := FloatArray.mk (u64AsFloats u)
  IO.println s!"u64->f {f.size} {f.toList.map Float.toBits}"
  -- shared source, used again
  let uf := u64AsFloats u
  IO.println s!"again {(FloatArray.mk uf).toList.map Float.toBits} {uf.size} {u.size}"
  let fl : Array Float := #[1.5, -0.0, Float.ofBits 0x7ff0000000000123]
  let back := floatsAsU64 fl
  IO.println s!"f->u64 {back} {(FloatArray.mk fl).toList.map Float.toBits}"
  let w : Array UInt32 := #[0, 255, 256, 0x12345678, 0xffffffff]
  IO.println s!"u32->u8 {(ByteArray.mk (u32AsBytes w)).toList}"
  IO.println s!"char->u8 {(ByteArray.mk (charsAsBytes #['a', 'é', '€', '😀'])).toList}"
  IO.println s!"bool->u8 {(ByteArray.mk (boolsAsBytes #[true, false, true])).toList}"
  IO.println s!"u16->u8 {(ByteArray.mk (u16AsBytes #[0x1ff, 0xfffe, 7])).toList}"
  let big : Array UInt64 := (Array.range 5000).map (fun (i : Nat) => (i.toUInt64 <<< (50 : UInt64)) ||| ((1 : UInt64) <<< (63 : UInt64)))
  IO.println s!"big {digFA (FloatArray.mk (u64AsFloats big))}"
