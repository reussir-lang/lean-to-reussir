/-! Runtime test (compact scalar arrays, plan "Tests": attach): the library
code that reads an array at another element type without a user cast.
`attach`, `attachWith`, `unattach` and `pmap` (Lean implements `attachWith`
by `unsafeCast` of the array to `Array {x // P x}`, natively the same
objects) on arrays of every storage kind, folds and maps over the attached
array, `Array.modify` (natively it leaves an `unsafeCast ()` placeholder in
the slot while the function runs) on unique and shared arrays and out of
bounds, arrays of a `Subtype` of `UInt8` and of `Float` built with
`filterMap` and read back, `mapFinIdx` and `for h : i in [:a.size]` with
the proof used for the index, `zipIdx`. -/

def mix (h x : UInt64) : UInt64 := (h ^^^ x) * 1099511628211

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 30
  let u8 : Array UInt8 := (Array.range n).map fun i => (i * 37 + 1).toUInt8
  let bo : Array Bool := (Array.range n).map fun i => i % 3 == 0
  let u16 : Array UInt16 := (Array.range n).map fun i => (i * 7919).toUInt16
  let u32 : Array UInt32 := (Array.range n).map fun i => (i * 2654435761).toUInt32
  let ch : Array Char := (Array.range n).map fun i => Char.ofNat (0x3B1 + i % 24)
  let u64 : Array UInt64 := (Array.range n).map fun i => i.toUInt64 * 0x9E3779B97F4A7C15 ||| 0x8000000000000000
  let us : Array USize := (Array.range n).map fun i => (i * 0x9E3779B97F4A7C15).toUSize
  let f32 : Array Float32 := (Array.range n).map fun i => (i.toFloat / 3.0).toFloat32
  let f64 : Array Float := (Array.range n).map fun i => if i == 4 then -0.0 else i.toFloat / 7.0 - 1.0
  -- attach and friends
  let a8 := u8.attach
  IO.println s!"u8 attach {a8.size} {a8.foldl (fun h x => mix h x.val.toUInt64) 7} {(a8.map (·.val + 1)).toList.take 5} {a8.unattach == u8}"
  let ab := bo.attachWith (fun _ => True) (fun _ _ => trivial)
  IO.println s!"bool attach {ab.size} {(ab.filter (·.val)).size} {(ab.unattach.map not).toList.take 4}"
  let a16 := u16.pmap (fun x (_ : x ∈ u16) => x.toUInt32 * 2) (fun _ h => h)
  IO.println s!"u16 pmap {a16.foldl (fun h x => mix h x.toUInt64) 7} {u16.attach.unattach == u16}"
  let a32 := u32.attach.map fun ⟨x, _⟩ => x >>> 4
  IO.println s!"u32 attach {a32.foldl (fun h x => mix h x.toUInt64) 7}"
  let ac := ch.attach
  IO.println s!"char attach {String.ofList (ac.unattach.toList.take 6)} {(ac.map (·.val.toUpper)).foldl (fun h x => mix h x.val.toUInt64) 7}"
  let a64 := u64.attach
  IO.println s!"u64 attach {a64.foldl (fun h x => mix h x.val) 7} {(a64.map (·.val ^^^ 1)).toList.take 2} {a64.unattach == u64}"
  let aus := us.attachWith (fun _ => True) (fun _ _ => trivial)
  IO.println s!"usize attach {aus.foldl (fun h x => mix h x.val.toUInt64) 7}"
  let af32 := f32.pmap (fun x (_ : x ∈ f32) => x.toFloat) (fun _ h => h)
  IO.println s!"f32 pmap {af32.foldl (fun h x => mix h x.toBits) 7}"
  let af := f64.attach
  IO.println s!"f64 attach {af.foldl (fun h x => mix h x.val.toBits) 7} {(af.map (·.val * 2)).toList.take 6} {af.unattach.size}"
  -- modify: unique, shared (the old array is printed), out of bounds
  let m8 := (u8.map (· + 0)).modify 3 (· + 100)
  let m8s := u8.modify 4 (· * 2)
  let m8o := u8.modify (n + 5) (· + 1)
  IO.println s!"modify u8 {m8[3]!} {m8s[4]!} {u8[4]!} {m8o == u8}"
  let mf := f64.modify 0 (· - 10.0) |>.modify 4 (fun x => -x)
  IO.println s!"modify f64 {mf[0]!} {mf[4]!} {f64[0]!} {f64[4]!}"
  let mu := u64.modify 1 (· ^^^ 0xFFFFFFFFFFFFFFFF)
  let mc := ch.modify 2 (fun c => Char.ofNat (c.toNat - 32))
  let mb := bo.modify 0 not
  let m16 := u16.modify 1 (· + 1)
  let m32 := u32.modify 1 (· + 1)
  let mus := us.modify 1 (· + 1)
  let mf32 := f32.modify 1 (· * 4)
  IO.println s!"modify {mu[1]!} {u64[1]!} {mc[2]!} {ch[2]!} {mb[0]!} {bo[0]!} {m16[1]!} {m32[1]!} {mus[1]!} {mf32[1]!} {f32[1]!}"
  let mut loopy := u8
  for i in [0:200] do
    loopy := loopy.modify (i % loopy.size) (· + i.toUInt8)
  IO.println s!"modify loop {loopy.foldl (fun h x => mix h x.toUInt64) 7} {u8.foldl (fun h x => mix h x.toUInt64) 7}"
  -- arrays of a Subtype
  let small : Array {x : UInt8 // x < 200} := u8.filterMap fun x => if h : x < 200 then some ⟨x, h⟩ else none
  let pos : Array {x : Float // x > 0} := f64.filterMap fun x => if h : x > 0 then some ⟨x, h⟩ else none
  IO.println s!"subtype {small.size} {(small.map (·.val)).toList.take 6} {small.unattach.foldl (fun h x => mix h x.toUInt64) 7} {pos.size} {(pos.unattach.map (· * 7)).toList.take 3}"
  -- proofs used for indices
  let byIdx := u16.mapFinIdx fun i x h => x.toUInt64 + (u16[i]'h).toUInt64 + i.toUInt64
  let mut s : UInt64 := 0
  for h : i in [:f64.size] do
    s := mix s (f64[i]'(Membership.get_elem_helper h rfl)).toBits
  IO.println s!"index {byIdx.foldl mix 7} {s} {(u8.zipIdx.map fun (x, i) => x.toNat + i).toList.take 5}"
