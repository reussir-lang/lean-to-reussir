import Std.Data.HashMap

/-! Runtime test (compact scalar arrays, plan "Tests": arrays inside
containers): scalar arrays inside `Prod` (updated through both fields in a
loop), `Option` (mapped, matched), `List` (a list of rows), `IO.Ref`
(`modify`, `modifyGet`, `swap`, a `get` that keeps the array shared before
a `modify`), `Task` (`Task.spawn`, `Task.map`, `Task.bind`, `IO.asTask`),
`Thunk` (forced twice, its array then updated by the caller), a structure
with array fields of four kinds (updated in place in a loop), `Except`,
`StateM` over an array state, `Std.HashMap` values, `Array (Array UInt8)`
rows updated in place and through shared rows, an `Array (Array Float)`
matrix product, and `Array (Array (Array Bool))`. Every array element type
here is a scalar of one storage kind. -/
def mix (h x : UInt64) : UInt64 := (h ^^^ x) * 1099511628211
def dU8 (a : Array UInt8) : UInt64 := a.foldl (fun h x => mix h x.toUInt64) 7
def dU16 (a : Array UInt16) : UInt64 := a.foldl (fun h x => mix h x.toUInt64) 7
def dU32 (a : Array UInt32) : UInt64 := a.foldl (fun h x => mix h x.toUInt64) 7
def dU64 (a : Array UInt64) : UInt64 := a.foldl mix 7
def dF (a : Array Float) : UInt64 := a.foldl (fun h x => mix h x.toBits) 7
def dF32 (a : Array Float32) : UInt64 := a.foldl (fun h x => mix h x.toBits.toUInt64) 7
def dB (a : Array Bool) : UInt64 := a.foldl (fun h x => mix h (if x then 1 else 2)) 7
def dC (a : Array Char) : UInt64 := a.foldl (fun h x => mix h x.val.toUInt64) 7

structure Buf where
  bytes : Array UInt8
  flags : Array Bool
  vals : Array Float
  wide : Array UInt64
  count : Nat

@[noinline] def Buf.step (b : Buf) (i : Nat) : Buf :=
  { b with
    bytes := b.bytes.push i.toUInt8 |>.set! (i % (b.bytes.size + 1)) 0xAA,
    flags := b.flags.push (i % 2 == 0),
    vals := if i % 3 == 0 then b.vals.push (i.toFloat / 3) else b.vals.set! 0 (b.vals[0]! + 1),
    wide := b.wide.push (0xFFFFFFFF00000000 + i.toUInt64),
    count := b.count + 1 }

def fill (n : Nat) : StateM (Array UInt16) Unit := do
  for i in [0:n] do
    modify (·.push (i * 1000).toUInt16)
    if i % 4 == 3 then modify (·.pop)
  let s ← get
  set (s.reverse)

def checked (a : Array UInt64) : Except String (Array UInt64) := do
  let mut r := a
  for i in [0:a.size] do
    if a[i]! == 0 then throw s!"zero at {i}"
    r := r.set! i (a[i]! * 2)
  return r

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 60
  -- Prod
  let mut p : Array UInt8 × Array Float := (#[], #[])
  for i in [0:n] do
    p := (p.1.push (i * 3).toUInt8, p.2.push (i.toFloat - 0.5))
  let p2 := Prod.map (·.reverse) (·.map (· * 2)) p
  IO.println s!"prod {dU8 p.1} {dF p.2} {dU8 p2.1} {dF p2.2} {p.1.size}"
  -- Option
  let mut o : Option (Array UInt64) := some #[]
  for i in [0:n] do
    o := o.map (·.push (i.toUInt64 <<< 60))
  let o2 : Option (Array UInt64) := o.bind fun a => if a.size > 1000 then none else some (a.pop)
  match o, o2 with
  | some a, some b => IO.println s!"option {dU64 a} {dU64 b} {a.size} {b.size}"
  | _, _ => IO.println "option none"
  -- List of rows
  let rows : List (Array UInt16) := (List.range 5).map fun r => (Array.range (r + n % 7)).map (·.toUInt16 * 9000)
  let rows2 := rows.map (·.push 65535)
  IO.println s!"list {rows.map dU16} {rows2.map dU16} {rows2.map (·.size)}"
  -- IO.Ref
  let ref ← IO.mkRef (#[] : Array Float32)
  for i in [0:n] do
    ref.modify (·.push (i.toFloat / 7.0).toFloat32)
  let sz ← ref.modifyGet fun a => (a.size, a.set! 0 (-1.0))
  let snap ← ref.get
  ref.modify (·.set! 1 (Float32.ofBits 0x7FC00000))
  let after ← ref.get
  let old ← ref.swap #[1.0, 2.0]
  let now ← ref.get
  IO.println s!"ref {sz} {dF32 snap} {snap[1]!} {dF32 after} {after[1]!} {dF32 old} {now.toList}"
  -- Task
  let t1 := Task.spawn fun _ => (Array.range n).map (fun i => (i * 2654435761).toUInt32)
  let t2 := t1.map fun a => a.map (fun (x : UInt32) => x >>> 3)
  let t3 := t2.bind fun a => Task.spawn fun _ => a.push 0xFFFFFFFF
  let t4 ← IO.asTask (do return (Array.range n).map (fun i => i % 5 == 0))
  IO.println s!"task {dU32 t1.get} {dU32 t2.get} {dU32 t3.get} {t3.get.size}"
  match t4.get with
  | .ok a => IO.println s!"asTask {dB a} {a.size}"
  | .error e => IO.println s!"asTask error {e}"
  -- Thunk
  let th : Thunk (Array Char) := Thunk.mk fun _ => (Array.range n).map fun i => Char.ofNat (0x3B1 + i % 24)
  let c1 := th.get
  let c2 := th.get.push 'Ω'
  IO.println s!"thunk {dC c1} {dC c2} {dC th.get} {c2.size} {String.ofList c1.toList |>.take 5}"
  -- a structure updated in place
  let mut b : Buf := ⟨#[1], #[], #[0.5], #[], 0⟩
  for i in [0:n] do
    b := b.step i
  IO.println s!"struct {dU8 b.bytes} {dB b.flags} {dF b.vals} {dU64 b.wide} {b.count}"
  -- StateM, Except
  let ((), st) := (fill n).run #[]
  IO.println s!"state {dU16 st} {st.size}"
  match checked ((Array.range n).map (·.toUInt64 + 1)) with
  | .ok r => IO.println s!"except ok {dU64 r}"
  | .error e => IO.println s!"except {e}"
  match checked ((Array.range n).map (·.toUInt64)) with
  | .ok r => IO.println s!"except ok {dU64 r}"
  | .error e => IO.println s!"except {e}"
  -- HashMap values
  let mut hm : Std.HashMap String (Array UInt64) := {}
  for i in [0:n] do
    hm := hm.alter s!"k{i % 4}" fun
      | some a => some (a.push (i.toUInt64 * 0x9E3779B97F4A7C15))
      | none => some #[i.toUInt64]
  let ks := ["k0", "k1", "k2", "k3", "k9"]
  IO.println s!"hashmap {ks.map fun k => (hm.getD k #[]).size} {ks.map fun k => dU64 (hm.getD k #[])}"
  -- Array (Array UInt8): in place (take the row out first), and through a shared row
  let mut grid : Array (Array UInt8) := (Array.range 6).map fun r => Array.replicate (r + 2) r.toUInt8
  for i in [0:n] do
    let r := i % grid.size
    let row := grid[r]!
    grid := grid.set! r #[]
    grid := grid.set! r (row.push (i.toUInt8 + 100))
  let shared := grid[2]!
  let grid2 := grid.set! 2 (grid[2]!.set! 0 77)
  IO.println s!"grid {grid.map dU8} {grid2.map dU8} {dU8 shared} {shared[0]!} {grid2[2]![0]!}"
  -- Array (Array Float): a matrix product
  let m := 6
  let a : Array (Array Float) := (Array.range m).map fun i => (Array.range m).map fun j => (i * m + j).toFloat / 10.0
  let bT : Array (Array Float) := (Array.range m).map fun j => (Array.range m).map fun i => if i == j then 2.0 else -0.5
  let prodM := a.map fun row => bT.map fun col => (row.zip col).foldl (fun s (x, y) => s + x * y) 0.0
  IO.println s!"matrix {prodM.map dF} {prodM[5]![5]!}"
  -- three levels
  let cube : Array (Array (Array Bool)) := (Array.range 3).map fun i => (Array.range 3).map fun j => (Array.range 4).map fun k => (i + j + k) % 2 == 0
  let cube2 := cube.modify 1 (·.modify 2 (·.set! 3 true |>.push false))
  IO.println s!"cube {cube.map (·.map dB)} {cube2.map (·.map dB)} {cube2[1]![2]!.size}"
