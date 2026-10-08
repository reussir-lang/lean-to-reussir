/-! Runtime test (compact scalar arrays, plan "Tests": a program that
casts): `unsafeCast` between scalar arrays whose elements native Lean
represents alike, so that the native result is defined:
- `Array UInt64` and `Array Float` (both boxed 8-byte cells natively): the
  bits, NaN payloads included, both ways, also after a `set!` on the view;
- `Array UInt64` and `Array USize` (both boxed 8-byte cells);
- `Array UInt8` read as `Array Bool` (values 0 and 1), as `Array UInt16`,
  `Array UInt32`, `Array Char` and `Array Nat` (all tagged scalars
  natively), and back; `Array UInt32` with values below 256 read as
  `Array UInt8`; an enum's array read as `Array UInt8` and back;
- a view updated while the original is still used (copy on write): the
  original keeps its values.
The plan turns compact storage off for every type a cast touches
(`programCasts`); `Array Float32`, which no cast touches, is used beside.
Not tested: `Array UInt64` read as `Array UInt8` and back. Natively a
`UInt64` element is a pointer to a cell and a `UInt8` element a tagged
scalar, so the `UInt8` view reads address bits and the `UInt64` view of
tagged scalars crashes: there is no native result to compare with. -/

inductive Col | red | green | blue
  deriving Repr, BEq, Inhabited

def mix (h x : UInt64) : UInt64 := (h ^^^ x) * 1099511628211

@[noinline] unsafe def view {α β : Type} (a : Array α) : Array β := unsafeCast a

unsafe def main (args : List String) : IO Unit := do
  let k := args.length.toUInt64
  -- UInt64 <-> Float
  let words : Array UInt64 := #[0x3FF0000000000000 + k, 0x7FF8000000000001 + k, 0xFFF0000000000003 + k,
    0x8000000000000000 + k, 0x7FF0000000000000 + k, 0x0000000000000001 + k, 0x400921FB54442D18 + k]
  let fs : Array Float := view words
  let back : Array UInt64 := view fs
  IO.println s!"u64>f64 {fs.toList} {back.toList} {back == words}"
  let fs2 := fs.set! 0 2.5
  let w2 : Array UInt64 := view fs2
  IO.println s!"f64 set {w2.toList} {words.toList}"
  let floats : Array Float := #[1.5 + k.toFloat, -0.0, 1.0 / 0.0, 0.1]
  let fw : Array UInt64 := view floats
  let fw2 := fw.set! 1 0x4000000000000000
  let floats2 : Array Float := view fw2
  IO.println s!"f64>u64 {fw.toList} {floats2.toList} {floats.toList}"
  -- UInt64 <-> USize
  let us : Array USize := view words
  let us2 := us.map (· + 1)
  let wu : Array UInt64 := view us2
  IO.println s!"u64>usize {us.toList} {wu.toList}"
  -- UInt8 views
  let bits01 : Array UInt8 := #[0, 1, 1, 0, (k % 2).toUInt8, 1]
  let bools : Array Bool := view bits01
  IO.println s!"u8>bool {bools.toList} {(bools.map not).toList} {(view (bools.map not) : Array UInt8).toList}"
  let bytes : Array UInt8 := #[0, 7, 127, 128, 200, 255, (k + 65).toUInt8]
  let w16 : Array UInt16 := view bytes
  let w32 : Array UInt32 := view bytes
  let wc : Array Char := view bytes
  let wn : Array Nat := view bytes
  IO.println s!"u8>wider {w16.toList} {w32.toList} {wc.toList.map Char.toNat} {wn.toList} {wn.foldl (· + ·) 0}"
  let wn2 := wn.map (· + 1000)
  let w16b := w16.map (· * 2)
  IO.println s!"wider updated {wn2.toList} {w16b.toList} {bytes.toList}"
  let small32 : Array UInt32 := #[1, 2, 250, 255, k.toUInt32]
  let n8 : Array UInt8 := view small32
  IO.println s!"u32>u8 {n8.toList} {(n8.map (· + 1)).toList}"
  let cols : Array Col := #[.red, .blue, .green, .blue]
  let c8 : Array UInt8 := view cols
  let c8b := c8.set! 0 2
  let colsB : Array Col := view c8b
  IO.println s!"col>u8 {c8.toList} {reprStr colsB.toList} {reprStr cols.toList}"
  -- a view updated while the original is used afterwards
  let orig : Array UInt8 := #[1, 0, 1, 1]
  let v : Array Bool := view orig
  let v2 := v.set! 0 false |>.push true
  IO.println s!"cow {v2.toList} {orig.toList} {(view v2 : Array UInt8).toList}"
  -- an array no cast touches
  let mut f32 : Array Float32 := #[]
  for i in [0:20] do
    f32 := f32.push (i.toFloat / 3.0).toFloat32
  IO.println s!"f32 {f32.foldl (fun h x => mix h x.toBits.toUInt64) 7} {f32.size}"
