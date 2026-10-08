/-! Runtime test (compact scalar arrays, plan "Lowering": `ByteArray.mk`
and `.data`, `FloatArray.mk` and `.data` become the identity for a compact
`Array UInt8` and `Array Float`): round trips, and the cases an identity
must not break: `ByteArray.mk` of a shared array, then the byte array
updated (the array keeps its values); `.data` of a shared byte array, then
the array updated (the byte array keeps its values); the same for
`FloatArray` (with -0.0, infinities and a NaN). Also the `ByteArray`
operations next to the `Array UInt8` ones (`push`, `set!`, `get!`,
`extract`, `++`, `copySlice`, `toList`, `foldl`), `String.toUTF8` and
`String.fromUTF8?` through `Array UInt8`, a `map` between the two
representations, and empty and literal arrays. -/

def mix (h x : UInt64) : UInt64 := (h ^^^ x) * 1099511628211
def dBA (b : ByteArray) : UInt64 := b.foldl (fun h x => mix h x.toUInt64) 7
def dU8 (a : Array UInt8) : UInt64 := a.foldl (fun h x => mix h x.toUInt64) 7
def dFA (a : FloatArray) : UInt64 := a.foldl (fun h x => mix h x.toBits) 7
def dF (a : Array Float) : UInt64 := a.foldl (fun h x => mix h x.toBits) 7

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 1000
  -- unique array to ByteArray and back
  let b1 := ByteArray.mk ((Array.range n).map fun i => (i * 37 + 1).toUInt8)
  let d1 := b1.data
  let b1b := ByteArray.mk d1
  IO.println s!"round {b1.size} {dBA b1} {dU8 d1} {dBA b1b} {b1b.data == d1}"
  -- ByteArray.mk of a shared array, then the byte array updated
  let a := (Array.range n).map fun i => (i * 11).toUInt8
  let b := ByteArray.mk a
  let b2 := (b.set! 0 0xEE).push 0xDD
  IO.println s!"mk shared {b2.get! 0} {b2.size} {a[0]!} {a.size} {dU8 a} {dBA b2} {dBA b}"
  -- .data of a shared byte array, then the array updated
  let c := ByteArray.mk ((Array.range n).map fun i => (i * 13).toUInt8)
  let ca := c.data
  let ca2 := (ca.set! 1 0x77).pop
  IO.println s!"data shared {ca2[1]!} {ca2.size} {c.get! 1} {c.size} {dBA c} {dU8 ca2}"
  -- FloatArray
  let fsrc : Array Float := (Array.range n).map fun i =>
    match i % 5 with
    | 0 => -0.0
    | 1 => 1.0 / 0.0
    | 2 => 0.0 / 0.0
    | _ => i.toFloat / 8.0
  let fa := FloatArray.mk fsrc
  let fa2 := (fa.set! 0 42.0).push (-(1.0 / 0.0))
  let fd := fa.data
  let fd2 := fd.set! 3 (-1.0)
  IO.println s!"floats {fa.size} {dFA fa} {dFA fa2} {fa2.get! 0} {fsrc[0]!} {dF fd} {dF fd2} {fa.get! 3} {fd2[3]!} {dF fsrc}"
  IO.println s!"floats round {dFA (FloatArray.mk fd)} {(FloatArray.mk fd).data.size} {fa.get! 1} {fa.get! 2}"
  -- ByteArray operations next to Array UInt8
  let mut ba := ByteArray.emptyWithCapacity 4
  let mut arr : Array UInt8 := #[]
  for i in [0:n] do
    ba := ba.push (i * 7).toUInt8
    arr := arr.push (i * 7).toUInt8
  ba := ba.set! 5 1
  arr := arr.set! 5 1
  IO.println s!"ops {dBA ba} {dU8 arr} {ba.data == arr} {ba.get! 9} {arr[9]!} {(ba.extract 3 9).toList} {(arr.extract 3 9).toList}"
  let cat := ba ++ b1
  let catA := arr ++ d1
  let sl := ba.copySlice 10 (ByteArray.mk (Array.replicate 20 0xFF)) 2 5
  IO.println s!"cat {dBA cat} {dU8 catA} {cat.data == catA} {sl.toList}"
  -- strings through Array UInt8
  let s := "héllo wörld ∀ 😀"
  let utf := s.toUTF8.data
  let shifted := ByteArray.mk (utf.map fun x => if x == 0x6C then 0x4C else x)
  IO.println s!"utf8 {utf.size} {String.fromUTF8? shifted} {String.fromUTF8? (ByteArray.mk (utf.pop))}"
  -- maps between the two representations
  let m1 := ByteArray.mk (b1.data.map (· ^^^ 0x5A))
  let m2 := FloatArray.mk (b1.data.map (·.toFloat))
  let m3 := ByteArray.mk (fa.data.map (·.toUInt8))
  IO.println s!"maps {dBA m1} {dFA m2} {dBA m3}"
  -- empty and literal
  let e := ByteArray.mk #[]
  let lit := ByteArray.mk #[1, 2, 3, 255]
  let fe := FloatArray.mk #[]
  let flit := FloatArray.mk #[1.5, -0.0]
  IO.println s!"small {e.size} {e.data.size} {lit.toList} {lit.data.reverse.toList} {fe.size} {flit.data.toList} {(ByteArray.mk (Array.replicate 3 7)).toList}"
