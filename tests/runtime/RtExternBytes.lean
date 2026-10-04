/-!
`@[extern]` declarations of the program over `ByteArray`s and structures,
in the shapes of lean-zip's C stopgaps (`Zip/Native/Wide.lean`,
`CopyWithin.lean`): a borrowed array read at a `USize` offset with an
in-bounds proof, an owned array written in place when exclusive (and copied
when shared, which the program observes), an append of the array's own
slice, a structure result with scalar and `Float` fields, a `Decidable`
result, and `IO` that throws. lean2rr compiles their Lean definitions
(translation plan §5.8, "Lean-only target"); natively the C code in
`RtExternBytes.ffi.c` runs, which agrees with them.
-/

namespace ByteArray

@[extern "rt_bytes_uget_u32le"]
def ugetU32LE (a : @& ByteArray) (off : USize) (h : off.toNat + 4 ≤ a.size) : UInt32 :=
  (a[off.toNat]'(by omega)).toUInt32 |||
  ((a[off.toNat + 1]'(by omega)).toUInt32 <<< 8) |||
  ((a[off.toNat + 2]'(by omega)).toUInt32 <<< 16) |||
  ((a[off.toNat + 3]'(by omega)).toUInt32 <<< 24)

protected theorem size_set' (a : ByteArray) (i : Nat) (v : UInt8) (h : i < a.size) :
    (a.set i v h).size = a.size := by
  simp only [← ByteArray.size_data, ByteArray.data_set, Array.size_set]

@[extern "rt_bytes_uset_u8x2"]
def usetU8x2 (a : ByteArray) (off : USize) (v : UInt16) (h : off.toNat + 2 ≤ a.size) : ByteArray :=
  (a.set off.toNat v.toUInt8 (by omega)).set (off.toNat + 1) (v >>> 8).toUInt8
    (by rw [ByteArray.size_set']; omega)

@[extern "rt_bytes_copy_within"]
def copyWithin (a : ByteArray) (srcOff len : Nat) : ByteArray :=
  a ++ a.extract srcOff (srcOff + len)

end ByteArray

structure P where
  x : UInt8
  y : Float
  s : String
deriving Repr

@[extern "rt_bytes_mk_p"]
def mkP (x : UInt8) (y : Float) (s : String) : P := { x := x + 1, y := y * 2, s := s ++ "!" }

@[extern "rt_bytes_dec_eq"]
def myDecEq (a b : @& Nat) : Decidable (a = b) := Nat.decEq a b

@[extern "rt_bytes_fail"]
def failIf (b : Bool) : IO Nat := do
  if b then throw (IO.userError "boom")
  return 7

/-- The sum of the little-endian words at every offset, read through the extern. -/
def wordSum (a : ByteArray) : UInt32 := Id.run do
  let mut acc : UInt32 := 0
  for i in [0:a.size] do
    if h : i.toUSize.toNat + 4 ≤ a.size then acc := acc + a.ugetU32LE i.toUSize h
  return acc

def main : IO Unit := do
  let a := ByteArray.mk ((List.range 40).map (fun i => (i * 37 % 256).toUInt8)).toArray
  IO.println (wordSum a)
  if h : (4 : USize).toNat + 4 ≤ a.size then IO.println (a.ugetU32LE 4 h)
  -- In place (exclusive), then on a shared array: the original is unchanged.
  let b := ByteArray.mk #[1, 2, 3, 4, 5]
  if h : (1 : USize).toNat + 2 ≤ b.size then
    let b' := b.usetU8x2 1 0xBEEF h
    IO.println (b'.toList, b.toList)
  let mut c := ByteArray.mk #[0, 0, 0, 0]
  for i in [0:3] do
    if h : i.toUSize.toNat + 2 ≤ c.size then c := c.usetU8x2 i.toUSize (i * 257 + 1).toUInt16 h
  IO.println c.toList
  -- Appends of the array's own slices, clamped at the end, and in a loop.
  let d := ByteArray.mk #[10, 20, 30, 40]
  IO.println ((d.copyWithin 1 2).toList, (d.copyWithin 3 9).toList, (d.copyWithin 7 1).toList)
  let mut g := ByteArray.mk #[1, 2]
  for _ in [0:5] do g := g.copyWithin 0 g.size
  IO.println (g.size, g.toList.take 6)
  IO.println (repr (mkP 255 1.5 "s"))
  IO.println (@ite _ (3 = 3) (myDecEq 3 3) "eq" "ne")
  IO.println (@decide (5 = 6) (myDecEq 5 6) || @decide _ (myDecEq 5 5))
  IO.println (← failIf false)
  try
    let v ← failIf true
    IO.println v
  catch e => IO.println s!"caught {e}"
