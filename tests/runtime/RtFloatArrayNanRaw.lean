/-! Runtime test (review of the runtime's speed items): raw NaN payloads and
-0.0 through `FloatArray.mk` and `FloatArray.data`, read back through
`unsafeCast`: the conversions copy the bits (no canonicalization). -/

@[noinline] unsafe def u64AsFloats (a : Array UInt64) : Array Float := unsafeCast a
@[noinline] unsafe def floatsAsU64 (a : Array Float) : Array UInt64 := unsafeCast a
@[noinline] unsafe def rawBits (x : Float) : UInt64 := (floatsAsU64 #[x])[0]!

unsafe def main : IO Unit := do
  let u : Array UInt64 := #[0x7ff0000000000123, 0xfff8000000000abc, 0x8000000000000000, 0x7ff4000000000001,
    0x7ff8000000000000, 0xffffffffffffffff, 0x0000000000000001, 0x3ff0000000000000, 5]
  let fa := FloatArray.mk (u64AsFloats u)
  IO.println s!"mk raw {fa.toList.map rawBits}"
  let d := fa.data
  IO.println s!"data raw {floatsAsU64 d}"
  IO.println s!"elem raw {(List.range fa.size).map fun i => rawBits fa[i]!}"
  let fa2 := FloatArray.mk d
  IO.println s!"round raw {(List.range fa2.size).map fun i => rawBits fa2[i]!} {fa.size}"
