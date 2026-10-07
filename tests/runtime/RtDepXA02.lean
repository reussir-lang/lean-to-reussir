import Std.Data.HashMap
/-! Runtime test: cases of the shared dependent-type corpus (programs built
by another translator's team and checked against native Lean), combined:
each case keeps its code in a namespace named after its case id, and `main`
runs each with that case's arguments in this order, printing `-- <id>`
before it (and `exit <code>` after a `main : IO UInt32`). The cases, with
what each checks:
- `A1023`: L16's shape: `AnyShape` (a value packed with its own `Shape`
  instance) built at `Circle`, `Rect` and `Poly` in a list that a loop reads
  through the packed instance
- `A1024`: L18's shape: `HashMap Point Nat` beside `Nat`- and `String`-keyed
  maps, all three started from `{}`, whose closed term Lean's compiler may
  share between the instantiations: the shared empty map keeps ...
- `A1025`: T15 step B7: a `Thunk (List α)` at a family position, built
  natively at `List Nat` and at `List String` and read by `total` at both,
  so `total` takes it at `Thunk (List Box)` and each caller converts ...
- `A1026`: T15 step B7's values with identity: an `IO.Ref (List α)` at a
  family position, read and written through `RP` at `List Nat` and at `List
  String` and also read and written natively, so the cell travels ...
- `A1027`: T15 step B7: a `Task (List α)` at a family position, spawned
  natively at `List Nat` and at `List String` and read by `total` at both,
  so `total` takes it at `Task (List Box)` and each caller converts ...
- `A1040`: A family position read under a dependent refinement.
- `A1041`: Steps B2 and B7: a free monad whose `liftBind`'s `ι` is `Nat` at
  `num` and `String` at `name` along one value.
- `A1042`: (ii): every open position of a boxing or unboxing site's type is
  `Box`.
- `A1043`: (ii), the reverse of A1042: `mkP` boxes `⟨true, 3⟩`, a `Pkg`
  built natively at `Nat`, while `mk`, another caller of `rd`, passes `Pkg`s
  built at both types, so `rd`'s slot is `Box` (step ...
- `A1044`: (iii): `run (getK (σ := Nat)) n` beside `run (getK (σ := String))
  ab`, whose one closed term `@getK ◾` Lean's compiler shares between the
  two instantiations.
- `A1045`: (iii): `@tw ◾ : Tw lcAny`, shared between `tw (σ := Nat)` and `tw
  (σ := String)`, holds `run : (Unit → σ) → List σ`, whose `σ` lies within
  an arrow's domain (the callback's result): each ... -/

namespace A1023

class Shape (α : Type) where
  name : α → String
  area : α → Float
  describe : α → String := fun s => s!"{name s} area={area s}"
structure Circle where r : Float
structure Rect where
  w : Float
  h : Float
structure Poly where
  sides : Nat
  len : Float
instance : Shape Circle where
  name _ := "circle"
  area c := 3.0 * c.r * c.r
instance : Shape Rect where
  name _ := "rect"
  area r := r.w * r.h
  describe r := s!"rect {r.w}x{r.h}"
instance : Shape Poly where
  name p := s!"{p.sides}-gon"
  area p := p.sides.toFloat * p.len * p.len / 4.0
structure AnyShape where
  {α : Type}
  [inst : Shape α]
  val : α
instance : Inhabited AnyShape := ⟨⟨Circle.mk 0.0⟩⟩
def AnyShape.area (s : AnyShape) : Float := s.inst.area s.val
def AnyShape.describe (s : AnyShape) : String := s.inst.describe s.val
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 7
  let k := n.toFloat
  let shapes : List AnyShape := [⟨Circle.mk k⟩, ⟨Rect.mk 2.0 k⟩, ⟨Poly.mk n 2.0⟩, ⟨Circle.mk 0.5⟩]
  let mut acc := 0.0
  for i in [0:n * 3] do
    acc := acc + shapes[i % shapes.length]!.area
  IO.println s!"{shapes.map (·.describe)} {acc}"
end A1023

namespace A1024

open Std
structure Point where
  x : Int
  y : Int
deriving BEq, Hashable, Repr
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 20
  let mut m : HashMap Nat Nat := {}
  for i in [0:n] do m := m.insert i (i * i)
  let mut s : HashMap String Nat := {}
  for i in [0:n] do s := s.insert (toString i) i
  let mut p : HashMap Point Nat := {}
  for i in [0:n] do p := p.insert ⟨i, -i⟩ i
  let pt : Point := ⟨3, -3⟩
  let q : Point := ⟨1, 1⟩
  IO.println s!"{m.size} {s.size} {p.size} {m[5]?} {s["7"]?} {p[pt]?} {p.contains q}"
end A1024

namespace A1025

structure TQ where
  b : Bool
  xs : Thunk (List (if b then Nat else String))
/-- A thunk built natively at `List Nat`, converted where it enters `TQ`. -/
@[noinline] def wrapN (t : Thunk (List Nat)) : TQ := ⟨true, t⟩
@[noinline] def mkN (n : Nat) (bad : Bool) : TQ :=
  wrapN (Thunk.mk fun _ => if bad then panic! "forced" else List.range n)
@[noinline] def mkS (s : String) : TQ := ⟨false, Thunk.mk fun _ => [s, s ++ s]⟩
@[noinline] def total (q : TQ) (force : Bool) : Nat :=
  if !force then 0 else
  match q with
  | ⟨true, t⟩ => t.get.foldl (· + ·) 0
  | ⟨false, t⟩ => t.get.foldl (fun a s => a + s.length) 0
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 5
  IO.println s!"{total (mkN n false) true} {total (mkS (toString n)) true} {total (mkN n true) false}"
end A1025

namespace A1026

structure RP where
  b : Bool
  r : IO.Ref (List (if b then Nat else String))
@[noinline] def bump (p : RP) : IO Unit := match p with
  | ⟨true, r⟩ => r.modify (fun (xs : List Nat) => xs.map (· + 1))
  | ⟨false, r⟩ => r.modify (fun (xs : List String) => xs.map (· ++ "!"))
@[noinline] def showRP (p : RP) : IO String := match p with
  | ⟨true, r⟩ => do let xs : List Nat := (← r.get); return toString xs
  | ⟨false, r⟩ => do let xs : List String := (← r.get); return toString xs
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let rn ← IO.mkRef (List.range n)
  let rs ← IO.mkRef ["a", toString n]
  let ps : List RP := [⟨true, rn⟩, ⟨false, rs⟩]
  for p in ps do bump p
  rn.modify (· ++ [100])
  for p in ps do IO.println (← showRP p)
  IO.println s!"{← rn.get} {← rs.get}"
end A1026

namespace A1027

structure TK where
  b : Bool
  t : Task (List (if b then Nat else String))
/-- A task spawned natively at `List Nat`, converted where it enters `TK`. -/
@[noinline] def wrapN (t : Task (List Nat)) : TK := ⟨true, t⟩
@[noinline] def mkN (n : Nat) : TK := wrapN (Task.spawn fun _ => List.range n)
@[noinline] def mkS (s : String) : TK := ⟨false, Task.spawn fun _ => [s, s ++ s]⟩
@[noinline] def total (q : TK) : Nat :=
  match q with
  | ⟨true, t⟩ => t.get.foldl (· + ·) 0
  | ⟨false, t⟩ => t.get.foldl (fun a s => a + s.length) 0
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 5
  IO.println s!"{total (mkN n)} {total (mkS (toString n))}"
end A1027

namespace A1040

structure Pkg where
  b : Bool
  v : if b then Nat else String

@[noinline] def mk (n : Nat) : Pkg := if n % 2 = 0 then ⟨true, (n : Nat)⟩ else ⟨false, toString n⟩

@[noinline] def rd : Pkg → Nat
  | ⟨true, v⟩ => let w : Nat := v; w + 1
  | ⟨false, _⟩ => 0

@[noinline] def sz : Pkg → Nat
  | ⟨true, _⟩ => 1
  | ⟨false, v⟩ => let s : String := v; s.length

def caseMain (args : List String) : IO Unit := do
  let n := args.length
  IO.println s!"{rd (mk (n + 1))} {rd (mk (n + 2))}"
  IO.println s!"{sz (mk (n + 11))} {sz (mk (n + 12))}"
end A1040

namespace A1041

inductive FreeM (F : Type → Type) (α : Type) where
  | pure : α → FreeM F α
  | liftBind {ι : Type} (op : F ι) (cont : ι → FreeM F α) : FreeM F α

inductive Q : Type → Type where
  | num : Q Nat
  | name : Q String

@[noinline] def prog (k : Nat) : FreeM Q Nat :=
  .liftBind .num fun n => .liftBind .name fun s => .pure (n * 10 + s.length + k)

@[noinline] def peel (p : FreeM Q Nat) : Option (Nat → FreeM Q Nat) :=
  match p with
  | .liftBind .num k => some k
  | _ => none

@[noinline] def run : FreeM Q Nat → Nat
  | .pure a => a
  | .liftBind op k => match op with
    | .num => run (k 4)
    | .name => run (k "abc")

def caseMain (args : List String) : IO Unit := do
  let k := args.length
  IO.println s!"{run (prog k)}"
  match peel (prog k) with
  | some c => IO.println s!"{run (c 7)}"
  | none => IO.println "none"
end A1041

namespace A1042

structure Pkg where
  b : Bool
  v : if b then Nat else String

@[noinline] def rd : Pkg → Nat
  | ⟨true, v⟩ => let w : Nat := v; w + 1
  | ⟨false, _⟩ => 0

@[noinline] def mkP : (c : Bool) → if c then Pkg else Nat
  | true => (⟨false, "s"⟩ : Pkg)
  | false => (5 : Nat)

@[noinline] def get : (c : Bool) → (if c then Pkg else Nat) → Nat
  | true, p => rd p
  | false, n => n

def caseMain (args : List String) : IO Unit := do
  IO.println (get args.isEmpty (mkP args.isEmpty))
end A1042

namespace A1043

structure Pkg where
  b : Bool
  v : if b then Nat else String

@[noinline] def rd : Pkg → Nat
  | ⟨true, v⟩ => let w : Nat := v; w + 1
  | ⟨false, _⟩ => 0

@[noinline] def mk (n : Nat) : Pkg := if n % 2 = 0 then ⟨true, (n : Nat)⟩ else ⟨false, toString n⟩

@[noinline] def mkP : (c : Bool) → if c then Pkg else Nat
  | true => (⟨true, (3 : Nat)⟩ : Pkg)
  | false => (5 : Nat)

@[noinline] def get : (c : Bool) → (if c then Pkg else Nat) → Nat
  | true, p => rd p
  | false, n => n

def caseMain (args : List String) : IO Unit := do
  IO.println (get args.isEmpty (mkP args.isEmpty))
  IO.println s!"{rd (mk args.length)} {rd (mk (args.length + 1))}"
end A1043

namespace A1044

inductive FreeM (F : Type → Type) (α : Type) where
  | pure : α → FreeM F α
  | liftBind {ι : Type} (op : F ι) (cont : ι → FreeM F α) : FreeM F α
inductive StateF (σ : Type) : Type → Type where
  | get : StateF σ σ
  | set : σ → StateF σ PUnit
@[noinline] def run {σ α : Type} : FreeM (StateF σ) α → σ → α × σ
  | .pure a, s => (a, s)
  | .liftBind op k, s => match op with
    | .get => run (k s) s
    | .set s' => run (k ()) s'
@[noinline] def getK {σ : Type} : FreeM (StateF σ) σ :=
  let k : σ → FreeM (StateF σ) σ := fun s => .pure s
  .liftBind .get k
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println s!"{run (getK (σ := Nat)) n} {run (getK (σ := String)) "ab"}"
  IO.println s!"{run (getK (σ := Nat)) (n + 1)} {run (getK (σ := String)) (toString n)}"
end A1044

namespace A1045

structure Tw (σ : Type) where
  run : (Unit → σ) → List σ
@[noinline] def tw {σ : Type} : Tw σ := ⟨fun f => [f (), f ()]⟩
def caseMain (a : List String) : IO Unit :=
  IO.println s!"{(tw (σ := Nat)).run (fun _ => a.length)} {(tw (σ := String)).run (fun _ => a.headD "ab")}"
end A1045

def main : IO Unit := do
  IO.println "-- A1023"
  A1023.caseMain ["x", "y"]
  IO.println "-- A1024"
  A1024.caseMain ["x", "y"]
  IO.println "-- A1025"
  A1025.caseMain ["x", "y"]
  IO.println "-- A1026"
  A1026.caseMain ["x", "y"]
  IO.println "-- A1027"
  A1027.caseMain ["x", "y"]
  IO.println "-- A1040"
  A1040.caseMain ["x", "y"]
  IO.println "-- A1041"
  A1041.caseMain ["x", "y"]
  IO.println "-- A1042"
  A1042.caseMain ["x", "y"]
  IO.println "-- A1043"
  A1043.caseMain ["x", "y"]
  IO.println "-- A1044"
  A1044.caseMain ["x", "y"]
  IO.println "-- A1045"
  A1045.caseMain ["x", "y"]
