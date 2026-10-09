/-! Runtime test (compact scalar arrays, hunt HARR2-01): `match b with |
⟨arr⟩ => ⟨arr.map f⟩` on a `ByteArray`, the program's only use of
`Array UInt8` that could turn the `u8` kind off. Lean's `toMono` binds
`arr` at `lcAny` to `ByteArray.data b`: before, the bytes were copied into
boxes (`l2r_boxes_of_bytes`), mapped by an untyped loop and copied back
(`l2r_bytes_of_boxes`), and the loop's `Array lcAny` met `ByteArray.mk`'s
`Array UInt8`, so `u8` went off and the unrelated `Array Bool` became an
array of boxes too. Now `arr` has the field's type `Array UInt8`, the
`map` runs in place over the bytes, and every kind stays on
(RtCArrMatchBytesMap.l2r-debug). -/
@[noinline] def bump (b : ByteArray) : ByteArray := match b with | ⟨arr⟩ => ⟨arr.map (· + 1)⟩

def main (args : List String) : IO Unit := do
  let n := args.length + 6
  let b : ByteArray := ⟨(Array.range n).map (·.toUInt8)⟩
  let flags : Array Bool := (Array.range n).map (· % 2 == 0)
  IO.println s!"{(bump b).toList} {flags.toList}"
