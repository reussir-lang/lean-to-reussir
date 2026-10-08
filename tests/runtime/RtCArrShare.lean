/-! Runtime test (compact scalar arrays, plan "Tests": shared and unique
arrays): copy on write for every storage kind. Each operation (`set!`,
`push`, `pop`, `swapIfInBounds`, `uset`, `reverse`, `++` of an array with
itself, an identity `map`, a same-kind `map`, `insertIdx!`, `eraseIdx!`,
`extract`) runs on a shared array, and the old array is printed after the
new one: it must be unchanged. A unique array updated in a loop, with a
snapshot kept every 7 steps (the snapshots must keep their contents), and
`dbgTraceIfShared` on a shared array of each kind (natively `shared RC
<kind>` on stderr) and on a unique one (nothing): each storage type needs
its own reference count check (as review HL-01 found for the boxed array
types). The sizes depend on the argument count so that no array is a
closed term (a persistent object natively). Last, constant arrays of each
kind (top-level literals, a computed table, a literal inside a loop)
updated by their users: the constants never change. -/

inductive Col | red | green | blue | cyan
  deriving Repr, BEq, Inhabited

instance : ToString Col := ⟨reprStr⟩
def Col.idx : Col → Nat | .red => 0 | .green => 1 | .blue => 2 | .cyan => 3

def mix (h x : UInt64) : UInt64 := (h ^^^ x) * 1099511628211

@[inline] def cow {α : Type} [ToString α] [Inhabited α] (name : String) (k : Nat)
    (mk : Nat → α) (f : α → α) (bits : α → UInt64) : IO Unit := do
  let dg (xs : Array α) : UInt64 := xs.foldl (fun h x => mix h (bits x)) 7
  let a : Array α := (Array.range (k + 6)).map mk
  let v := mk 1000
  let b := a.set! 0 v
  let c := a.push v
  let d := a.pop
  let e := a.swapIfInBounds 0 (a.size - 1)
  let g := if h : (1 : USize).toNat < a.size then a.uset 1 v h else a
  let r := a.reverse
  let s := a ++ a
  let m := a.map (fun x => x)
  let m2 := a.map f
  let ins := a.insertIdx! 2 v
  let er := a.eraseIdx! 1
  let ex := a.extract 1 4
  IO.println s!"{name} new {b[0]!} {c.back!} {d.size} {e[0]!} {g[1]!} {r[0]!} {s.size} {dg m} {dg m2} {ins[2]!} {er[1]!} {ex.toList}"
  IO.println s!"{name} digests {dg b} {dg c} {dg d} {dg e} {dg g} {dg r} {dg s} {dg ins} {dg er}"
  IO.println s!"{name} old {a.toList} {dg a}"
  -- a unique array updated in place, snapshots kept
  let mut x := (Array.range (k + 10)).map mk
  let mut snaps : List (Array α) := []
  for i in [0:30] do
    if i % 7 == 0 then snaps := x :: snaps
    x := x.set! (i % x.size) (mk (i * 3 + 1))
    x := x.swapIfInBounds (i % x.size) ((i + 3) % x.size)
  IO.println s!"{name} snaps {dg x} {snaps.map dg} {(snaps.map (·[0]!)).toString}"
  -- reference counts: `a` is read again after the trace (a fold no earlier
  -- code computes, so that Lean's common subexpression elimination cannot
  -- move the read before the trace), so it is shared at the trace
  let t := dbgTraceIfShared name a
  let after := a.foldl (fun h x => mix h (bits x)) 99
  IO.println s!"{name} rc {t.size} {after}"
  let u := (Array.range (k + 3)).map mk
  let u' := dbgTraceIfShared (name ++ " unique") u
  IO.println s!"{name} rc unique {u'.size}"

-- constant arrays (natively persistent objects, never updated in place)
def tblU8 : Array UInt8 := #[1, 2, 3, 250, 255]
def tblBool : Array Bool := #[true, false, true]
def tblU16 : Array UInt16 := #[0, 65535, 300]
def tblU32 : Array UInt32 := #[0xFFFFFFFF, 7]
def tblChar : Array Char := #['a', '€', '😀']
def tblU64 : Array UInt64 := #[0xFFFFFFFFFFFFFFFF, 0x8000000000000000, 5]
def tblUSize : Array USize := #[0xFFFFFFFFFFFFFFFF, 3]
def tblF32 : Array Float32 := #[1.5, -0.0, 3.25]
def tblF64 : Array Float := #[1.5, -0.0, 1e300]
def tblTable : Array UInt64 := (Array.range 64).map fun i => i.toUInt64 * i.toUInt64 * 0x9E3779B97F4A7C15

@[inline] def constUse {α : Type} [ToString α] [Inhabited α] (name : String) (tbl : Array α)
    (f : α → α) (bits : α → UInt64) : IO Unit := do
  let dg (xs : Array α) : UInt64 := xs.foldl (fun h x => mix h (bits x)) 7
  let mut ds : Array UInt64 := #[]
  for i in [0:6] do
    let j := i % tbl.size
    let x := (tbl.set! j (f tbl[j]!)).push tbl[j]!
    ds := ds.push (dg x)
  IO.println s!"{name} const {ds} {tbl.toList} {dg tbl}"

def main (args : List String) : IO Unit := do
  let k := args.length
  cow "u8" k (fun i => (i * 37 + 1).toUInt8) (· + 1) (·.toUInt64)
  cow "bool" k (fun i => i % 3 == 1) not (fun b => if b then 1 else 0)
  cow "col" k (fun i => match i % 4 with | 0 => Col.red | 1 => .green | 2 => .blue | _ => .cyan)
    (fun c => if c == Col.red then Col.cyan else Col.red) (fun c => c.idx.toUInt64)
  cow "u16" k (fun i => (i * 7919 + 3).toUInt16) (· * 3) (·.toUInt64)
  cow "u32" k (fun i => (i * 2654435761).toUInt32) (· ^^^ 0xFFFFFFFF) (·.toUInt64)
  cow "char" k (fun i => Char.ofNat (0x1F600 + i % 50)) (fun c => Char.ofNat (c.toNat + 1)) (·.val.toUInt64)
  cow "u64" k (fun i => i.toUInt64 * 0x9E3779B97F4A7C15 ||| 0x8000000000000000) (· + 1) id
  cow "usize" k (fun i => (i * 0x9E3779B97F4A7C15).toUSize) (· - 1) (·.toUInt64)
  cow "f32" k (fun i => (i.toFloat / 3.0 - 1.0).toFloat32) (fun x => -x) (·.toBits.toUInt64)
  cow "f64" k (fun i => if i == 2 then -0.0 else i.toFloat / 7.0 - 1.0) (· * 0.5) Float.toBits
  constUse "u8" tblU8 (· + 1) (·.toUInt64)
  constUse "bool" tblBool not (fun b => if b then 1 else 0)
  constUse "u16" tblU16 (· + 1) (·.toUInt64)
  constUse "u32" tblU32 (· + 1) (·.toUInt64)
  constUse "char" tblChar (fun c => Char.ofNat (c.toNat + 1)) (·.val.toUInt64)
  constUse "u64" tblU64 (· + 1) id
  constUse "usize" tblUSize (· + 1) (·.toUInt64)
  constUse "f32" tblF32 (· * 2) (·.toBits.toUInt64)
  constUse "f64" tblF64 (· * 2) Float.toBits
  constUse "table" tblTable (· ^^^ 0xFF) id
  -- a literal inside a loop: every iteration starts from the literal
  let mut acc : List (List UInt16) := []
  for i in [0:4] do
    let lit : Array UInt16 := #[10, 20, 30]
    acc := (lit.set! (i % 3) (i.toUInt16 * 1000) |>.push 7).toList :: acc
  IO.println s!"literal {acc}"
