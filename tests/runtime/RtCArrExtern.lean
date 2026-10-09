/-! Runtime test (compact scalar arrays and the externs of the program): a
program whose `@[extern]` declarations have Lean definitions, over
`ByteArray`, `Array UInt8`, `Array UInt64` and `Array Float`, in the
shapes of lean-zip's (`Zip/Native/Wide.lean`'s `ByteArray.ugetUInt32LE`,
`Zip/Native/InflateFast.lean`'s `ByteArray.presize`), and an extern bound to
an `@[export]` definition of the program (`checksum`). lean2rr runs their
Lean code (translation plan §5.8, "Lean-only target"), which reads no
value as another type, so the program does not cast and every compact
kind stays on (`RtCArrExtern.l2r-debug`). Until then every extern of the
program, and every `@[export]`, made the program one that can cast
(`programCasts`), which turned every compact kind off (lean-zip's decoder
then stored its output as an array of boxes, 8 bytes per byte) and
`unread-fields` with them. Natively the C code in `RtCArrExtern.ffi.c`
runs, and `checksum`'s call is linked to `checksumImpl`. -/

namespace ByteArray

@[extern "rt_carr_uget_u32le"]
def ugetU32LE (a : @& ByteArray) (off : USize) (h : off.toNat + 4 ≤ a.size) : UInt32 :=
  (a[off.toNat]'(by omega)).toUInt32 |||
  ((a[off.toNat + 1]'(by omega)).toUInt32 <<< 8) |||
  ((a[off.toNat + 2]'(by omega)).toUInt32 <<< 16) |||
  ((a[off.toNat + 3]'(by omega)).toUInt32 <<< 24)

@[extern "rt_carr_presize"]
def presize (n : @& Nat) : ByteArray := ByteArray.mk (Array.replicate n 0)

end ByteArray

/-- Each byte plus `k`. -/
@[extern "rt_carr_bump"]
def bump (a : Array UInt8) (k : UInt8) : Array UInt8 := a.map (· + k)

/-- The little-endian words of `a`, eight bytes each (the last bytes that
make no word are left out). -/
@[extern "rt_carr_words"]
def words (a : @& ByteArray) : Array UInt64 := Id.run do
  let mut out : Array UInt64 := #[]
  for i in [0:a.size / 8] do
    let mut w : UInt64 := 0
    for j in [0:8] do
      w := w ||| (a.get! (8 * i + j)).toUInt64 <<< (8 * j).toUInt64
    out := out.push w
  return out

/-- Each float times `f`. -/
@[extern "rt_carr_scale"]
def scale (a : @& Array Float) (f : Float) : Array Float := a.map (· * f)

@[export rt_carr_checksum]
def checksumImpl (a : ByteArray) : UInt64 := a.foldl (fun h x => (h ^^^ x.toUInt64) * 1099511628211) 7

@[extern "rt_carr_checksum"]
opaque checksum : ByteArray → UInt64

def main (args : List String) : IO Unit := do
  let k := args.length
  let n := 1000 + k
  -- A buffer made by the extern, filled in place.
  let mut b := ByteArray.presize n
  for i in [0:n] do
    b := b.set! i ((i * 37 + k) % 256).toUInt8
  let mut acc : UInt32 := 0
  for i in [0:n] do
    if h : i.toUSize.toNat + 4 ≤ b.size then acc := acc + b.ugetU32LE i.toUSize h
  IO.println s!"bytes {b.size} {b.get! 0} {b.get! (n - 1)} u32 sum {acc}"
  -- `Array UInt8` in and out, and back to a `ByteArray`.
  let a2 := bump b.data 3
  let b2 := ByteArray.mk a2
  IO.println s!"bump {a2.size} {a2[0]!} {a2[n - 1]!} checksums {checksum b} {checksum b2}"
  -- `Array UInt64` and `Array Float` results.
  let ws := words b2
  IO.println s!"words {ws.size} {ws[0]!} {ws.foldl (· ^^^ ·) 0}"
  let fs := scale (ws.map fun w => (w % 1000).toFloat) 0.5
  IO.println s!"floats {fs.size} {fs[0]!} {fs.foldl (· + ·) 0.0}"
