/-! `unsafeCast` between `Float` and `UInt64` (and `Float32`/`UInt32`) at a
boxed position copies the bits unchanged, NaN sign and payload included
(round 6, U1). Values are computed at run time: the sign of a NaN that an
operation produces is unspecified, and compile-time folding may differ. -/

@[noinline] unsafe def castImpl {α β : Type} [Inhabited β] (x : α) : β := unsafeCast x
@[implemented_by castImpl] opaque cast' {α β : Type} [Inhabited β] (x : α) : β

@[noinline] def zero (n : Nat) : Float := n.toFloat

def main (args : List String) : IO Unit := do
  let z := zero args.length
  let nan := z / z
  let a : UInt64 := cast' nan
  let b : UInt64 := cast' (-nan)
  IO.println s!"nan bits {a} {b}"
  let payload : UInt64 := 0x7ff0000000000001 + args.length.toUInt64
  let f : Float := cast' payload
  let back : UInt64 := cast' f
  IO.println s!"payload kept {back == payload} {back}"
  let neg : UInt64 := cast' (-(1.5 + z))
  IO.println s!"neg {neg}"
  let p32 : UInt32 := 0x7f800001 + args.length.toUInt32
  let f32 : Float32 := cast' p32
  let back32 : UInt32 := cast' f32
  IO.println s!"payload32 kept {back32 == p32}"
