/-! Runtime test (compact scalar arrays, hunt HARR2-01): `match b with |
⟨arr⟩` on a `ByteArray` and on a `FloatArray`. Lean's `toMono` binds `arr`
at `lcAny` to `ByteArray.data b` (`FloatArray.data b`): the data stayed a
box, a `map` over it ran over boxes (its loop could not be typed), and the
loop's `Array lcAny` met `FloatArray.mk`'s `Array Float`, so `f64` went off
for the whole program; the list of an `Array UInt8` taken apart in a loop
turned `u8` off (on dev 0b6ef980 both were off here). Now `arr` has the field's type (`Array UInt8`,
`Array Float`): `mk` and `data` are the identity, the `map` loops are
typed, and every kind stays on (RtCArrMatchBytes.l2r-debug). Also the
bytes read, updated and rebuilt, `.data` of a byte array that stays in use
(the identity must keep it unchanged), and both fields of a structure
taken apart in a loop (`flatten-structs` passes them at their own types). -/
@[noinline] def viaMatch (b : ByteArray) : Nat := match b with | ⟨arr⟩ => arr.foldl (fun s x => s + x.toNat) 0
@[noinline] def rebuild (b : ByteArray) : ByteArray := match b with | ⟨arr⟩ => ⟨(arr.push 7).reverse⟩
@[noinline] def viaMatchF (b : FloatArray) : FloatArray := match b with | ⟨arr⟩ => ⟨arr.map (· * 2)⟩
@[noinline] def sumF (b : FloatArray) : Float := match b with | ⟨arr⟩ => arr.foldl (· + ·) 0
@[noinline] def sharedThenPush (b : ByteArray) : ByteArray × ByteArray := match b with | ⟨arr⟩ => (⟨arr.push 1⟩, b)
@[noinline] def floats (b : FloatArray) : List Float := match b with | ⟨arr⟩ => arr.toList

structure S where
  data : Array UInt8
  fs : FloatArray
  n : Nat

@[noinline] def loop (s : S) (i : Nat) : S :=
  if i = 0 then s else
  match s.data, s.fs with
  | ⟨l⟩, ⟨fa⟩ => loop { s with data := ⟨(l.map (· + 1)).reverse⟩, fs := ⟨fa.map (· + 0.5)⟩, n := s.n + l.length } (i - 1)

def main (args : List String) : IO Unit := do
  let n := args.length + 6
  let b : ByteArray := ⟨(Array.range n).map (·.toUInt8)⟩
  let f : FloatArray := ⟨(Array.range n).map (·.toFloat)⟩
  let a : Array UInt8 := b.data.push 1
  IO.println s!"{viaMatch b} {(rebuild b).toList} {(viaMatchF f).toList} {a.toList} {b.toList}"
  let (b1, b2) := sharedThenPush b
  IO.println s!"{b1.toList} {b2.toList} {b.size} {sumF f} {floats ⟨(Array.range n).map (·.toFloat / 3)⟩}"
  let s := loop ⟨(Array.range n).map (·.toUInt8), ⟨(Array.range n).map (·.toFloat)⟩, 0⟩ 3
  IO.println s!"{s.data} {s.fs.toList} {s.n}"
