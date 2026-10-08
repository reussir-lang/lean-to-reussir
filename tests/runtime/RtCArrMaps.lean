/-! Runtime test (compact scalar arrays, plan "Tests" and "Typed map
loops"): `Array.map` within one storage kind (in place when the source is
unique) and across kinds (`UInt64` to `UInt8`, `UInt8` to `UInt64`,
`Float` to `UInt64` by value and by bits, `UInt64` to `Float`, `Float` to
`Float32` and back, `Bool` to `UInt32`, `UInt32` to `Bool`, `Char` to
`UInt8` and back, an enum to `Bool`, `UInt16` to `Float32`, `USize` to
`UInt16`), to and from a boxed element type (`Nat`, `String`, `Option`),
`mapIdx` and `mapFinIdx` across kinds, `mapM` in `IO`, `StateM` and
`Except` (an early exit), `mapMono`, `zip`, `zipWith`, `unzip`,
`filterMap`, `flatMap`, maps of empty and one-element arrays, chains of
maps, a map repeated 1000 times on a unique array, and maps of a shared
source whose source is printed afterwards (natively the map's loop copies
the shared array at its first write; a compact map of another kind writes
a new array). Natively `Array.map` runs `Array.mapMUnsafe`, which writes
each result into the source array cast to the result type; the compact
plan lowers these loops as typed loops. -/

inductive Col | red | green | blue
  deriving Repr, BEq, Inhabited

def mix (h x : UInt64) : UInt64 := (h ^^^ x) * 1099511628211
def dU8 (a : Array UInt8) : UInt64 := a.foldl (fun h x => mix h x.toUInt64) 7
def dU16 (a : Array UInt16) : UInt64 := a.foldl (fun h x => mix h x.toUInt64) 7
def dU32 (a : Array UInt32) : UInt64 := a.foldl (fun h x => mix h x.toUInt64) 7
def dU64 (a : Array UInt64) : UInt64 := a.foldl mix 7
def dF (a : Array Float) : UInt64 := a.foldl (fun h x => mix h x.toBits) 7
def dF32 (a : Array Float32) : UInt64 := a.foldl (fun h x => mix h x.toBits.toUInt64) 7
def dB (a : Array Bool) : UInt64 := a.foldl (fun h x => mix h (if x then 1 else 2)) 7
def dC (a : Array Char) : UInt64 := a.foldl (fun h x => mix h x.val.toUInt64) 7

@[noinline] def mkU64 (n : Nat) : Array UInt64 :=
  (Array.range n).map fun i => i.toUInt64 * 0x9E3779B97F4A7C15 + 0x8000000000000000
@[noinline] def mkU8 (n : Nat) : Array UInt8 := (Array.range n).map fun i => (i * 37 + 5).toUInt8
@[noinline] def mkF (n : Nat) : Array Float :=
  (Array.range n).map fun i =>
    match i % 7 with
    | 0 => 0.0 / 0.0
    | 1 => -0.0
    | 2 => 1.0 / 0.0
    | 3 => -(1.0 / 0.0)
    | 4 => 1.0e19 + i.toFloat * 1.0e18
    | _ => (i.toFloat - 20.0) * 1.25

-- maps in other monads
def stMap (a : Array UInt8) : StateM UInt64 (Array UInt64) :=
  a.mapM fun x => do modify (mix · x.toUInt64); return (← get)
def exMap (a : Array UInt16) : Except String (Array Float32) :=
  a.mapM fun x => if x ≥ 0xF000 then throw s!"stop at {x}" else pure (x.toNat.toFloat.toFloat32 / 4)

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 50
  let u64 := mkU64 n
  let u8 := mkU8 n
  let f := mkF n
  -- across kinds, sources shared (printed again at the end)
  let a1 : Array UInt8 := u64.map (·.toUInt8)
  let a2 : Array UInt64 := u8.map (fun x => (x.toUInt64 <<< (56 : UInt64)) ||| x.toUInt64)
  let a3 : Array UInt64 := f.map Float.toUInt64
  let a4 : Array UInt64 := f.map Float.toBits
  let a5 : Array Float := u64.map UInt64.toFloat
  let a6 : Array Float32 := f.map Float.toFloat32
  let a7 : Array Float := a6.map Float32.toFloat
  IO.println s!"u64>u8 {dU8 a1} {a1.toList.take 6}"
  IO.println s!"u8>u64 {dU64 a2} {a2.toList.take 3}"
  IO.println s!"f>u64 {dU64 a3} {a3.toList.take 7}"
  IO.println s!"f>bits {dU64 a4} {a4.toList.take 7}"
  IO.println s!"u64>f {dF a5} {a5.toList.take 3}"
  IO.println s!"f>f32>f {dF32 a6} {dF a7} {a7.toList.take 7}"
  let bools : Array Bool := u8.map (· % 3 == 0)
  let a8 : Array UInt32 := bools.map (fun b => if b then 0xFFFFFFFF else 7)
  let a9 : Array Bool := a8.map (· > 100)
  IO.println s!"bool>u32>bool {dU32 a8} {dB a9} {a9 == bools}"
  let chars : Array Char := u8.map (fun x => Char.ofNat (0x41 + x.toNat % 26))
  let a10 : Array UInt8 := chars.map Char.toUInt8
  let a11 : Array Char := a10.map (fun x => Char.ofNat (x.toNat + 0x3B1 - 0x41))
  IO.println s!"char>u8>char {dC chars} {dU8 a10} {dC a11} {String.ofList (a11.toList.take 8)}"
  let cols : Array Col := u8.map (fun x => if x % 3 == 0 then .red else if x % 3 == 1 then .green else .blue)
  let a12 : Array Bool := cols.map (· == .green)
  IO.println s!"col>bool {dB a12} {(a12.filter id).size} {reprStr (cols.toList.take 4)}"
  let u16 : Array UInt16 := u8.map (fun x => x.toUInt16 * 257)
  let a13 : Array Float32 := u16.map (fun x => x.toNat.toFloat.toFloat32 / 3)
  let us : Array USize := u64.map UInt64.toUSize
  let a14 : Array UInt16 := us.map USize.toUInt16
  IO.println s!"u16>f32 {dF32 a13} usize>u16 {dU16 a14} {a14.toList.take 4}"
  -- within a kind; the second map of each pair runs on a unique array
  let w1 := (u8.map (· + 1)).map (· * 3)
  let w2 := (f.map (· * 2)).map (fun x => -x)
  let w3 := (u64.map (fun (x : UInt64) => x ^^^ 0xFFFF)).map (fun (x : UInt64) => x >>> 1)
  let w4 := (bools.map not).map not
  let w5 := chars.map Char.toLower
  IO.println s!"within {dU8 w1} {dF w2} {dU64 w3} {dB w4} {w4 == bools} {dC w5}"
  -- to and from boxed element types
  let nats : Array Nat := u64.map (·.toNat * 3)
  let back : Array UInt64 := nats.map (fun x => (x / 3).toUInt64)
  let strs : Array String := f.map toString
  let lens : Array UInt8 := strs.map (·.length.toUInt8)
  let opts : Array (Option Float) := f.map (fun x => if x.isNaN then none else some x)
  let unopt : Array Float := opts.map (·.getD 42.0)
  IO.println s!"boxed {nats.foldl (· + ·) 0} {back == u64} {strs.toList.take 5} {dU8 lens} {dF unopt}"
  -- mapIdx, mapFinIdx across kinds
  let mi : Array UInt64 := u8.mapIdx (fun i x => i.toUInt64 * 1000 + x.toUInt64)
  let mf : Array Float := u64.mapFinIdx (fun i x _ => if i % 2 == 0 then x.toFloat else i.toFloat)
  let mb : Array Bool := f.mapIdx (fun i x => x > i.toFloat)
  IO.println s!"idx {dU64 mi} {dF mf} {dB mb}"
  -- mapM
  let cnt ← IO.mkRef 0
  let mio ← u8.mapM fun x => do
    cnt.modify (· + 1)
    pure (x.toFloat / 8)
  let (ms, st) := (stMap u8).run 3
  IO.println s!"mapM {dF mio} {← cnt.get} {dU64 ms} {st}"
  match exMap u16 with
  | .ok r => IO.println s!"except ok {dF32 r}"
  | .error e => IO.println s!"except {e}"
  match exMap (u16.filter (· < 0xF000)) with
  | .ok r => IO.println s!"except ok {dF32 r}"
  | .error e => IO.println s!"except {e}"
  -- mapMono (the identity map keeps the array), zip, zipWith, unzip, filterMap, flatMap
  let mm := u8.mapMono id
  let mm2 := u8.mapMono (· + 0)
  let mm3 := f.mapMono (· + 1)
  let z := u8.zip f
  let zw : Array UInt64 := u16.zipWith (fun a b => a.toUInt64 * 65536 + b.toUInt64) a8
  let (zu8, zf) := z.unzip
  let fm : Array UInt8 := u64.filterMap (fun x => if x % 3 == 0 then some x.toUInt8 else none)
  let fl : Array Float32 := u8.flatMap (fun x => #[x.toNat.toFloat.toFloat32, -1])
  IO.println s!"misc {dU8 mm} {dU8 mm2} {dF mm3} {z.size} {dU64 zw} {zu8 == u8} {dF zf} {dU8 fm} {fm.size} {dF32 fl}"
  -- empty and one element
  let e : Array UInt64 := #[]
  let one : Array UInt8 := #[200]
  IO.println s!"small {(e.map (·.toUInt8)).size} {(one.map (·.toFloat)).toList} {(one.map (fun x => x == 200)).toList} {((#[] : Array Float).map Float.toBits).size}"
  -- a map repeated on a unique array, within a kind and through another kind and back
  let mut acc := mkU8 1000
  let mut accF := mkF 1000
  for i in [0:1000] do
    acc := acc.map (· + i.toUInt8)
    accF := (accF.map Float.toBits).map (fun b => Float.ofBits (b ^^^ 1))
  IO.println s!"repeat {dU8 acc} {dF accF}"
  -- the shared sources are unchanged
  IO.println s!"sources {dU64 u64} {dU8 u8} {dF f} {dB bools} {dC chars} {dU16 u16}"
