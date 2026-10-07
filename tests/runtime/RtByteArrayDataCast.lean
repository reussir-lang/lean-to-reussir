/-! Runtime test: `ByteArray.mk`, `ByteArray.data`, `FloatArray.mk` and
`FloatArray.data` in a program that casts (it has an `unsafeCast`), where
unboxing at `UInt8` or `Float` reads an object through the generated cast:
lean2rr checks the boxes first (`l2r_boxes_all_imm`,
`l2r_boxes_all_float_words`) and converts in one loop when they are what
the plain unboxing reads, else element by element. An `Array UInt8` cast
from an `Array String` takes the second path; only its size is printed
(natively the bytes are bits of addresses). -/

def mix (h x : UInt64) : UInt64 := (h ^^^ x) * 1099511628211

@[noinline] def digB (b : ByteArray) : UInt64 := b.foldl (fun h x => mix h x.toUInt64) 7
@[noinline] def digFA (a : FloatArray) : UInt64 := a.foldl (fun h x => mix h x.toBits) 7

@[noinline] unsafe def strsAsBytes (a : Array String) : Array UInt8 := unsafeCast a

@[noinline] def mkBytes (n : Nat) : Array UInt8 := (Array.range n).map fun i => (i * 7 + 3).toUInt8

unsafe def main : IO Unit := do
  for n in [0, 1, 9, 300, 70000] do
    let a := mkBytes n
    let b := ByteArray.mk a
    IO.println s!"bytes {n}: {b.size} {digB b} {b.data.size} {b.data == a}"
  let f := FloatArray.mk ((Array.range 100).map fun i => i.toFloat / 3.0)
  IO.println s!"floats {f.size} {digFA f} {(FloatArray.mk f.data).size} {digFA (FloatArray.mk f.data)}"
  let odd := strsAsBytes #["a", "bc", "def"]
  IO.println s!"cast {(ByteArray.mk odd).size}"
