/-! Runtime test: cases of the shared dependent-type corpus (programs built
by another translator's team and checked against native Lean), combined:
each case keeps its code in a namespace named after its case id, and `main`
runs each with that case's arguments in this order, printing `-- <id>`
before it (and `exit <code>` after a `main : IO UInt32`). The cases, with
what each checks:
- `A996`: Rule E4 and step 11: a runner whose only uses lie inside a map
  helper's lambda (`a.map fun p => (run p n).2`): E4 sees no instantiation
  there, and the conversion of the array's `FreeM` elements ...
- `A997`: Steps 1 and 11 (A): `ap List.length ["a", "b"] + ap List.length
  [k]`, whose closed term `List.length` Lean's compiler shares between `List
  String` and `List Nat` (NS19): it must translate correctly or ...
- `A998`: And step 11 (A): a rank-2 parameter `h : {ι : Type} → List ι →
  Nat` called at `List Nat` and `List String` inside a `for` loop
  (`lenLoop`, whose loop body Lean specializes ...
- `A999`: A heterogeneous container over an existential (`Pkg` with a type
  field `α` and a value `val : α`), a `List Pkg` built in a `map` lambda
  from constructors at `Nat`, `String` and `List Nat`, ...
- `A1111`: polymorphic recursion across a mutual block calling the partner
  at its own type argument and at Nat; no list conversion between the two
  instances
- `A1310`: a dependent pair (Σ b : Bool, F b) built with both first
  components in an Array.map closure and summed by a fold (binders with no
  name)
- `A1300`:
- `A1301`:
- `A1302`:
- `A1303`:
- `A1304`: -/

namespace A996

inductive FreeM (F : Type → Type) (α : Type) where
  | pure : α → FreeM F α
  | liftBind {ι : Type} (op : F ι) (cont : ι → FreeM F α) : FreeM F α

inductive StateF (σ : Type) : Type → Type where
  | get : StateF σ σ
  | set : σ → StateF σ PUnit

/-- One `ι` type only (`σ` at both operations): must stay native. -/
inductive PeekF (σ : Type) : Type → Type where
  | peek : PeekF σ σ
  | poke : σ → PeekF σ σ

@[noinline] def getS {σ : Type} : FreeM (StateF σ) σ := .liftBind .get .pure
@[noinline] def setS {σ : Type} (s : σ) : FreeM (StateF σ) PUnit := .liftBind (.set s) .pure

@[noinline] def run {σ α : Type} : FreeM (StateF σ) α → σ → α × σ
  | .pure a, s => (a, s)
  | .liftBind op k, s => match op with
    | .get => run (k s) s
    | .set s' => run (k ()) s'

@[noinline] def runPeek {σ α : Type} : FreeM (PeekF σ) α → σ → α × σ
  | .pure a, s => (a, s)
  | .liftBind op k, s => match op with
    | .peek => runPeek (k s) s
    | .poke s' => runPeek (k s') s'

@[noinline] def peeks : Nat → FreeM (PeekF Nat) Nat
  | 0 => .liftBind .peek .pure
  | n+1 => .liftBind (.poke n) fun s => .liftBind .peek fun t => match peeks n with
    | .pure r => .pure (r + s + t)
    | o => o

structure Prog where
  name : String
  body : FreeM (StateF Nat) Nat
  alt : Option (FreeM (StateF Nat) Nat)

@[noinline] def mkProg (n : Nat) : Prog :=
  { name := s!"p{n}", body := .liftBind .get fun s => .liftBind (.set (s + n)) fun _ => .pure s,
    alt := if n % 2 == 0 then some getS else none }

@[noinline] def runAll (ps : List Prog) (s : Nat) : List (Nat × Nat) :=
  ps.map fun p => match p.alt with
    | some a => run a s
    | none => run p.body s

@[noinline] def liftBindAfter (p : FreeM (StateF Nat) PUnit) : FreeM (StateF Nat) Nat :=
  .liftBind .get fun s => match p with
    | .pure _ => .pure s
    | .liftBind op k => .liftBind op (fun x => match k x with | _ => .pure (s + 1))
@[noinline] def arrOf (n : Nat) : Array (FreeM (StateF Nat) Nat) :=
  (Array.range n).map fun i => if i % 3 == 0 then getS else liftBindAfter (setS i)

/-- `StateF PUnit`: `ι` is `PUnit` at both operations. -/
@[noinline] def unitProg : Nat → FreeM (StateF PUnit) Nat
  | 0 => .pure 0
  | n+1 => .liftBind .get fun _ => .liftBind (.set ()) fun _ => (unitProg n)

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let a := arrOf (n % 9 + 2)
  IO.println s!"{(a.map fun p => (run p n).2).toList}"
end A996

namespace A997

@[noinline] def ap {α β : Type} (f : α → β) (x : α) : β := f x
def caseMain (args : List String) : IO Unit := do
  let k := args.length
  IO.println s!"{ap List.length ["a", "b"] + ap List.length [k]}"
end A997

namespace A998

@[noinline] def lenLoop (h : {ι : Type} → List ι → Nat) (xs : List Nat) (s : String) (k : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:k] do
    acc := acc + h xs + h [s]
  return acc
@[noinline] def lenFold (h : {ι : Type} → List ι → Nat) (xs : List Nat) (s : String) (k : Nat) : Nat :=
  (List.range k).foldl (fun acc _ => acc + h xs + h [s, s]) 0
@[noinline] def lenRec (h : {ι : Type} → List ι → Nat) (xs : List Nat) (s : String) : Nat → Nat
  | 0 => 0
  | k+1 => h xs + h [s] + lenRec h xs s k
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let xs := List.range (n % 12 + 1)
  IO.println s!"{lenLoop (fun l => l.reverse.length) xs "i" (n % 50)} {xs.length}"
  IO.println s!"{lenFold (fun l => (l.drop 1).length + 1) xs "f" (n % 40)}"
  IO.println s!"{lenRec (fun l => l.length) xs "r" (n % 30)}"
end A998

namespace A999

structure Pkg where
  α : Type
  val : α
  tag : Nat
@[noinline] def pkgN (n : Nat) : Pkg := ⟨Nat, n, n % 7⟩
@[noinline] def pkgS (s : String) : Pkg := ⟨String, s, s.length⟩
@[noinline] def pkgL (l : List Nat) : Pkg := ⟨List Nat, l, l.length⟩
def caseMain (args : List String) : IO Unit := do
  let n := ((args[0]?).bind String.toNat?).getD 10
  let ps : List Pkg := (List.range n).map fun i => if i % 3 == 0 then pkgN i else if i % 3 == 1 then pkgS (toString i) else pkgL (List.range (i % 5))
  let arr : Array Pkg := ps.toArray.push (pkgN 99)
  IO.println s!"{ps.foldl (fun a p => a + p.tag) 0} {arr.size} {(arr.map (·.tag)).foldl (· + ·) 0}"
end A999

namespace A1111

mutual
@[noinline] def qA {α : Type} (xs : List α) : Nat → Nat
  | 0 => xs.length
  | n + 1 => qB xs n + n
@[noinline] def qB {α : Type} (xs : List α) : Nat → Nat
  | 0 => 3
  | n + 1 => qA xs n + qA [n] n + 1
end
def caseMain (args : List String) : IO Unit := do
  let k := args.length
  IO.println (qA args (k + 4))
end A1111

namespace A1310
def F (b : Bool) : Type := if b then Nat else String

def size : (Σ b : Bool, F b) → Nat
  | ⟨true, v⟩ => (v : Nat)
  | ⟨false, v⟩ => (v : String).length

def caseMain (args : List String) : IO Unit := do
  let xs : Array Nat := (List.range (args.length + 3)).toArray
  let ys := xs.map fun (x : Nat) => if x % 2 == 0 then (⟨true, (show F true from x)⟩ : Σ b : Bool, F b) else ⟨false, (show F false from (toString x : String))⟩
  IO.println (ys.foldl (fun acc y => acc + size y) 0)
end A1310

namespace A1300

@[noinline] def f1 (x : Nat) (_ : Type) : Nat := dbgTrace s!"f1 {x}" fun _ => x + 1
@[noinline] def f2 (x : Nat) (_ : Type) (_ : Type) : Nat := dbgTrace s!"f2 {x}" fun _ => x * 2
@[noinline] def applyN (h : Type → Nat) (m : Nat) : Nat := (List.range m).foldl (fun acc i => acc + h Nat + i) 0
@[noinline] def atFirst (h : Type → Type → Nat) : Type → Nat := h Nat
structure Holder where
  run : Type → Nat
  tag : Nat
@[noinline] def useHolder (h : Holder) (m : Nat) : Nat := applyN h.run m + h.tag

def caseMain (args : List String) : IO Unit := do
  let n := args.length
  let g := f1 n
  let hs : List (Type → Nat) := [f1 (n + 1), f1 (n + 2), g]
  let h := Holder.mk (f1 (n + 3)) n
  let k := atFirst (f2 n)
  IO.eprintln "== made"
  IO.println s!"{applyN g (n + 2)}"
  IO.eprintln "== list"
  IO.println s!"{hs.foldl (fun acc v => acc + v Nat) 0}"
  IO.eprintln "== second erased argument"
  IO.println s!"{applyN k (n + 1)}"
  IO.eprintln "== field"
  IO.println s!"{useHolder h 2}"
end A1300

namespace A1301

@[noinline] def g1 (_ : Type) : Nat := dbgTrace "g1" fun _ => 7
@[noinline] def g2 {_ : Type} (_ : Type) : Nat := dbgTrace "g2" fun _ => 9
@[noinline] def callN (h : Type → Nat) (k : Nat) : Nat :=
  (List.range k).foldl (fun acc i => acc + h Nat + i) 0

def caseMain (args : List String) : IO Unit := do
  let k := args.length + 1
  let vs : List (Type → Nat) := [g1, @g2 String, g1]
  IO.eprintln "== made"
  IO.println s!"{callN g1 k}"
  IO.eprintln "== g2"
  IO.println s!"{callN (@g2 Nat) k}"
  IO.eprintln "== list"
  IO.println s!"{vs.foldl (fun acc h => acc + h Bool) k}"
  IO.eprintln "== closed"
  IO.println s!"{g1 Nat + g1 Nat + k}"
end A1301

namespace A1302

@[noinline] def h3 (_ : Type) (x : Nat) (_ : Type) (y : Nat) : Nat := dbgTrace s!"h3 {x} {y}" fun _ => x + y
@[noinline] def useA (p : Type → Nat → Type → Nat → Nat) (a : Nat) : Nat := p Nat a Bool 1 + p String a Nat 2
@[noinline] def useB (p : Nat → Type → Nat → Nat) (a : Nat) : Nat :=
  let q := p a
  let r := q Bool
  r 3 + r 4 + q Nat 5
@[noinline] def useC (p : Type → Nat → Nat) : Nat := p Nat 6 + p Bool 7
@[noinline] def useD (p : Nat → Nat) : Nat := p 8 + p 9
structure Box3 where
  f : Type → Nat → Nat

def caseMain (args : List String) : IO Unit := do
  let n := args.length
  let pB := h3 Nat
  let pC := h3 Nat n
  let pD := h3 Nat (n + 1) String
  let ds : List (Nat → Nat) := [pD, h3 Bool n Nat]
  let b := Box3.mk (h3 String (n + 2))
  IO.eprintln "== made"
  IO.println s!"{useA h3 n}"
  IO.println s!"{useB pB n}"
  IO.println s!"{useC pC}"
  IO.println s!"{useD pD}"
  IO.println s!"{ds.foldl (fun acc f => acc + f 10) 0}"
  IO.println s!"{b.f Nat 11 + b.f Bool 12}"
end A1302

namespace A1303

@[noinline] def constT {β : Sort u} {γ : Type v} (b : γ) (_ : β) : γ := dbgTrace "constT" fun _ => b
@[noinline] def pre : Type → Nat → Nat := fun _ => dbgTrace "pre" fun _ => fun n => n + 1
structure Rest where
  k : Nat → Nat
@[noinline] def atType (h : Type → Nat → Nat) : Rest := ⟨h Nat⟩
@[noinline] def loopK (r : Rest) (m : Nat) : Nat := (List.range m).foldl (fun acc i => acc + r.k i) 0
@[noinline] def run2 (h : Type → Nat → Nat) (a : Nat) : Nat :=
  let k := h Nat
  k a + k (a + 1)
structure Op where
  run : Type → Nat → Nat
@[noinline] def runOp (o : Op) (a : Nat) : Nat := o.run Bool a

def caseMain (args : List String) : IO Unit := do
  let n := args.length
  let k : Nat → Nat := fun x => dbgTrace s!"k {x}" fun _ => x + n
  let hs : List (Type → Nat → Nat) := [constT k, fun _ x => dbgTrace s!"post {x}" fun _ => x * 2, pre]
  IO.eprintln "== made"
  IO.println s!"{hs.foldl (fun acc h => acc + loopK (atType h) (n + 2)) 0}"
  IO.eprintln "== run2"
  IO.println s!"{hs.foldl (fun acc h => acc + run2 h n) 0}"
  IO.eprintln "== field"
  IO.println s!"{(hs.map Op.mk).foldl (fun acc o => acc + runOp o (n + 5)) 0}"
end A1303

namespace A1304

@[noinline] def constT {β : Sort u} {γ : Type v} (b : γ) (_ : β) : γ := dbgTrace "constT" fun _ => b
@[noinline] def c3 : Type → Type → Nat := fun _ => dbgTrace "c3 first" fun _ => fun _ => dbgTrace "c3 second" fun _ => 7
structure Rest where
  k : Type → Nat
@[noinline] def atFirst (h : Type → Type → Nat) : Rest := ⟨h Nat⟩
@[noinline] def loopT (r : Rest) (m : Nat) : Nat := (List.range m).foldl (fun acc i => acc + r.k Bool + i) 0

def caseMain (args : List String) : IO Unit := do
  let n := args.length
  let c : Type → Nat := fun _ => dbgTrace s!"c {n}" fun _ => n + 5
  let hs : List (Type → Type → Nat) := [constT c, fun _ _ => dbgTrace s!"second {n}" fun _ => n + 6, c3]
  IO.eprintln "== made"
  IO.println s!"{hs.foldl (fun acc h => acc + loopT (atFirst h) (n + 2)) 0}"
  IO.eprintln "== direct"
  IO.println s!"{hs.foldl (fun acc h => acc + h String Nat) n}"
end A1304

def main : IO Unit := do
  IO.println "-- A996"
  A996.caseMain ["a", "b", "c"]
  IO.println "-- A997"
  A997.caseMain ["a", "b", "c"]
  IO.println "-- A998"
  A998.caseMain ["0"]
  IO.println "-- A999"
  A999.caseMain ["0"]
  IO.println "-- A1111"
  A1111.caseMain ["x", "y"]
  IO.println "-- A1310"
  A1310.caseMain ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j"]
  IO.println "-- A1300"
  A1300.caseMain ["x", "y"]
  IO.println "-- A1301"
  A1301.caseMain ["x", "y"]
  IO.println "-- A1302"
  A1302.caseMain ["x", "y"]
  IO.println "-- A1303"
  A1303.caseMain ["x", "y"]
  IO.println "-- A1304"
  A1304.caseMain ["x", "y"]
