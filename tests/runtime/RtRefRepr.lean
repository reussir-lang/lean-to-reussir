/-! Runtime test: `IO.Ref`/`ST.Ref` contents in their own representation
(translation plan §5.1). References of `Nat` and `Int` across the small/big
boundary, of arrays updated in place by `modify`, of strings, lists,
enumerations, `[value]` structures, floats, functions and thunks; a
reference created by typed code and used by uniform code (existential
packages reading it at other representations), and the reverse; `ptrEq`
between aliases seen at different representations; references in
structures, arrays and `initialize` constants; `StateRefT` and `runST`. -/

inductive Dir | n | e | s | w deriving Repr, BEq, Inhabited

structure W where
  n : Nat
deriving Repr

structure Ctx where
  hits : IO.Ref Nat
  log : IO.Ref (Array String)
  name : String

-- existential packages: the reference is read at another representation
structure PkgA where
  α : Type
  r : IO.Ref (Nat → α)

structure PkgB where
  α : Type
  β : Type
  r : IO.Ref (α → β)

structure PkgN where
  α : Type
  r : IO.Ref α

@[noinline] def touchA (p : PkgA) : IO Unit := do p.r.set (← p.r.get)
@[noinline] def touchB (p : PkgB) : IO Unit := do p.r.set (← p.r.get)
@[noinline] def touchN (p : PkgN) : IO Unit := do
  let v ← p.r.get
  p.r.set v
-- uniform code comparing references
@[noinline] unsafe def sameRefU (p q : PkgN) : IO Bool := ST.Ref.ptrEq p.r (unsafeCast q.r)
@[implemented_by sameRefU] opaque sameRef (p q : PkgN) : IO Bool

/-- A reference created where its element type is unknown. -/
structure Mk where
  α : Type
  v : α
  show' : α → String

@[noinline] def viaUniform (m : Mk) : IO String := do
  let r ← IO.mkRef m.v
  let x ← r.get
  r.set x
  let y ← r.swap x
  return m.show' y

initialize gCount : IO.Ref Nat ← IO.mkRef 5

def bump (c : Ctx) (k : Nat) : IO Unit := do
  c.hits.modify (· + k)
  if k % 3 == 0 then c.log.modify (·.push s!"{c.name}{k}")

def countUp (n : Nat) : StateRefT Nat IO Unit := do
  for i in [0:n] do
    modify (· + i % 7)

def stSum (n : Nat) : Nat := runST fun σ => show ST σ Nat from do
  let r ← ST.mkRef (σ := σ) (0 : Nat)
  for i in [0:n] do
    r.modify (· + i)
  r.get

def stStruct (n : Nat) : W × Int := runST fun σ => show ST σ (W × Int) from do
  let r ← ST.mkRef (σ := σ) ({ n := 1 } : W)
  let q ← ST.mkRef (σ := σ) (-3 : Int)
  for i in [0:n] do
    r.modify fun w => { n := w.n * 2 + i }
    q.modify (· * -2)
  return (← r.get, ← q.get)

def main (args : List String) : IO Unit := do
  let k := args.length + 1
  -- Nat across 2^63 and 2^64, and back to small
  let rn ← IO.mkRef (2 ^ 62 : Nat)
  for _ in [0:3] do
    rn.modify (· * 2)
    IO.println s!"nat {← rn.get}"
  rn.set (2 ^ 64 - 1)
  IO.println s!"nat max {← rn.get} {← rn.modifyGet fun x => (x + 1, x + 2)} {← rn.get}"
  let old ← rn.swap 7
  IO.println s!"nat swap {old} {← rn.get}"
  rn.modify (· + 2 ^ 100)
  rn.modify (· - 2 ^ 100)
  IO.println s!"nat back {← rn.get}"
  -- Int with negatives and big values
  let ri ← IO.mkRef (-(2 ^ 61 : Int))
  for _ in [0:4] do
    ri.modify (· * 2)
    IO.println s!"int {← ri.get}"
  ri.set 0
  ri.modify (· - 5)
  IO.println s!"int small {← ri.get}"
  -- arrays updated in place, strings, lists, options, pairs
  let ra ← IO.mkRef (#[] : Array Nat)
  for i in [0:1000] do
    ra.modify (·.push i)
  let rs ← IO.mkRef "a"
  for _ in [0:5] do rs.modify (· ++ "b")
  let rl ← IO.mkRef ([] : List Nat)
  for i in [0:5] do rl.modify (i :: ·)
  let ro ← IO.mkRef (none : Option Nat)
  ro.set (some 41)
  ro.modify (·.map (· + 1))
  let rp ← IO.mkRef ((1, "x") : Nat × String)
  rp.modify fun (a, b) => (a + 1, b ++ "y")
  IO.println s!"arr {(← ra.get).size} {(← ra.get).foldl (· + ·) 0} str {← rs.get} list {← rl.get} opt {← ro.get} pair {← rp.get}"
  -- enumerations, Bool, Unit, UInt8, Float, Char, a [value] structure
  let rd ← IO.mkRef Dir.n
  rd.modify fun | .n => .e | .e => .s | .s => .w | .w => .n
  let rb ← IO.mkRef false
  rb.modify (!·)
  let ru ← IO.mkRef ()
  ru.set ()
  let r8 ← IO.mkRef (250 : UInt8)
  for _ in [0:10] do r8.modify (· + 1)
  let rf ← IO.mkRef (1.5 : Float)
  rf.modify (· * 3.0)
  let rc ← IO.mkRef 'a'
  rc.modify fun c => Char.ofNat (c.toNat + 1)
  let rw ← IO.mkRef ({ n := 3 } : W)
  rw.modify fun w => { n := w.n + 2 ^ 70 }
  IO.println s!"dir {repr (← rd.get)} bool {← rb.get} unit {(← ru.get) == ()} u8 {← r8.get} float {← rf.get} char {← rc.get} w {repr (← rw.get)}"
  -- references in structures and arrays
  let c : Ctx := { hits := ← IO.mkRef 0, log := ← IO.mkRef #[], name := "c" }
  for i in [0:10] do bump c (i * k)
  let refs ← (List.range 4).toArray.mapM fun i => IO.mkRef (i * 10)
  for r in refs do r.modify (· + 1)
  let vals ← refs.mapM (·.get)
  IO.println s!"ctx {← c.hits.get} {← c.log.get} arr refs {vals}"
  -- an `initialize` constant
  gCount.modify (· * 3)
  IO.println s!"global {← gCount.get}"
  -- typed references read by uniform code at other representations
  let r ← IO.mkRef (fun (x : Nat) => x + 1)
  let pa : PkgA := ⟨Nat, r⟩
  let pb : PkgB := ⟨Nat, Nat, r⟩
  let mut acc := 0
  for i in [0:20] do
    touchA pa
    touchB pb
    acc := acc + (← r.get) i
  IO.println s!"fn {acc} {(← r.get) 41}"
  let rt ← IO.mkRef (Thunk.mk fun _ => ((1 : Nat), (2 : Nat)))
  let pt : PkgN := ⟨Thunk (Nat × Nat), rt⟩
  for _ in [0:5] do touchN pt
  IO.println s!"thunk {(← rt.get).get}"
  let pn : PkgN := ⟨Nat, rn⟩
  touchN pn
  let pn2 : PkgN := ⟨Nat, rn⟩
  let pi : PkgN := ⟨Int, ri⟩
  IO.println s!"ptrEq {← sameRef pn pn2} {← sameRef pn pi} {← sameRef pi pi} {← ST.Ref.ptrEq rn rn} {← rn.get}"
  -- references created by uniform code
  IO.println s!"uniform {← viaUniform ⟨Nat, 2 ^ 65, toString⟩} {← viaUniform ⟨String, "s", id⟩} {← viaUniform ⟨Dir, .w, fun d => repr d |>.pretty⟩}"
  -- StateRefT and runST
  let ((), s) ← (countUp (1000 * k)).run 0
  IO.println s!"stateRefT {s} st {stSum 1000} {repr (stStruct 10)}"
