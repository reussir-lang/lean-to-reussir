import Std.Data.HashMap
/-! Runtime test: cases of the shared dependent-type corpus (programs built
by another translator's team and checked against native Lean), combined:
each case keeps its code in a namespace named after its case id, and `main`
runs each with that case's arguments in this order, printing `-- <id>`
before it (and `exit <code>` after a `main : IO UInt32`). The cases, with
what each checks:
- `D71TesterT27`: Rep_B: function values at several kinds and arities, and a
  Thunk, boxed and unboxed at one class
- `D71TesterT28`: B2 (iii) arrow domain: a shared value whose class reaches
  an arrow's domain (getK-like reader/writer, a callback result in a
  structure)
- `D71TesterT28A`: B2 (iii) arrow domain: a shared value whose class reaches
  an arrow's domain (getK-like reader/writer, a callback result in a
  structure)
- `D71TesterT28B`: B2 (iii) arrow domain: a shared value whose class reaches
  an arrow's domain (getK-like reader/writer, a callback result in a
  structure)
- `D71TesterT28C`: B2 (iii) arrow domain: a shared value whose class reaches
  an arrow's domain (getK-like reader/writer, a callback result in a
  structure)
- `D71TesterT29`: B5 Unit placeholder: Array.modify on an array of boxed
  values (box(0) stored during the modify), and an existential with a type-
  valued field
- `D71TesterT30`: A shared closed term (List.reverse []) read in generic
  code: a conversion generic in the reader's parameters
- `D71TesterT31`: B2 (iii): a closed map erase read at two value types
  (closedTwoTypes), then used
- `D71TesterT33`: B2 (i) per-use agreement through a wrapper: ap2 forwards
  to ap
- `D71TesterT35`: A function value reaching a Box position and an FnOnce
  primitive (Thunk.mk / Task.spawn): Fn with clones
- `D71TesterT37`: B2 (iii) arrow domain variants: shared closed FreeM terms
  whose results hold the state at List σ, Option σ, σ × Nat -/

namespace D71TesterT27
structure AnyF where
  {α : Type}
  f : α → Nat → String
  x : α
@[noinline] def two (a : Nat) (b : Nat) : String := s!"{a}+{b}"
@[noinline] def AnyF.run (s : AnyF) (k : Nat) : String := s.f s.x k
@[noinline] def mkCurried (p : String) : String → Nat → String := fun s => fun k => p ++ s ++ toString k
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let t : Thunk Nat := Thunk.mk fun _ => n * 7
  let xs : List AnyF := [⟨two, n⟩, ⟨mkCurried s!"c{n}", "s"⟩, ⟨fun (th : Thunk Nat) k => toString (th.get + k), t⟩,
    ⟨fun (g : Nat → Nat) k => toString (g k), (· * n)⟩, ⟨fun (l : List Nat) k => toString (l.map (· + k)), List.range n⟩]
  IO.println (xs.map (·.run 5))
  IO.println (xs.map (·.run n))
end D71TesterT27

namespace D71TesterT28
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
@[noinline] def swapK {σ : Type} : FreeM (StateF σ) (σ × σ) :=
  .liftBind .get fun a => .liftBind (.set a) fun _ => .liftBind .get fun b => .pure (a, b)
structure Tw (σ : Type) where
  run : (Nat → σ) → Nat → List σ
@[noinline] def tw {σ : Type} : Tw σ := ⟨fun f n => (List.range n).map f⟩
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println s!"{run (swapK (σ := Nat)) n} {run (swapK (σ := String)) "ab"} {run (swapK (σ := List Nat)) [n]}"
  IO.println s!"{(tw (σ := Nat)).run (· * 2) n} {(tw (σ := String)).run (s!"x{·}") n} {(tw (σ := Bool)).run (· > 1) n}"
end D71TesterT28

namespace D71TesterT28A
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
@[noinline] def swapK {σ : Type} : FreeM (StateF σ) (σ × σ) :=
  .liftBind .get fun a => .liftBind (.set a) fun _ => .liftBind .get fun b => .pure (a, b)
structure Tw (σ : Type) where
  run : (Nat → σ) → Nat → List σ
@[noinline] def tw {σ : Type} : Tw σ := ⟨fun f n => (List.range n).map f⟩
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println s!"{run (swapK (σ := Nat)) n} {run (swapK (σ := String)) "ab"} {run (swapK (σ := List Nat)) [n]}"
end D71TesterT28A

namespace D71TesterT28B
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
@[noinline] def swapK {σ : Type} : FreeM (StateF σ) (σ × σ) :=
  .liftBind .get fun a => .liftBind (.set a) fun _ => .liftBind .get fun b => .pure (a, b)
structure Tw (σ : Type) where
  run : (Nat → σ) → Nat → List σ
@[noinline] def tw {σ : Type} : Tw σ := ⟨fun f n => (List.range n).map f⟩
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println s!"{(tw (σ := Nat)).run (· * 2) n} {(tw (σ := String)).run (s!"x{·}") n} {(tw (σ := Bool)).run (· > 1) n}"
end D71TesterT28B

namespace D71TesterT28C
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
@[noinline] def swapK {σ : Type} : FreeM (StateF σ) (σ × σ) :=
  .liftBind .get fun a => .liftBind (.set a) fun _ => .liftBind .get fun b => .pure (a, b)
structure Tw (σ : Type) where
  run : (Nat → σ) → Nat → List σ
@[noinline] def tw {σ : Type} : Tw σ := ⟨fun f n => (List.range n).map f⟩
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println s!"{run (swapK (σ := Nat)) n} {run (swapK (σ := String)) "ab"}"
end D71TesterT28C

namespace D71TesterT29
structure AnyS where
  {α : Type}
  [inst : ToString α]
  val : α
@[noinline] def AnyS.show (s : AnyS) : String := s.inst.toString s.val
@[noinline] def bumpAt (xs : Array AnyS) (i : Nat) : Array AnyS := xs.modify i fun s => ⟨s.show ++ "#"⟩
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let xs : Array AnyS := #[⟨n⟩, ⟨s!"s{n}"⟩, ⟨decide (n > 2)⟩]
  let ys := bumpAt (bumpAt xs 1) (n % 3)
  IO.println (ys.map (·.show))
  IO.println (xs.map (·.show))
end D71TesterT29

namespace D71TesterT30
@[noinline] def toListR {α : Type} (xs : Array α) : List α := (xs.foldl (fun acc a => a :: acc) []).reverse
@[noinline] def twice {β : Type} (xs : Array β) : List β := toListR xs ++ toListR xs
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println s!"{toListR (Array.range n)} {toListR #["a", toString n]} {twice #[decide (n > 1)]} {(twice (Array.range n)).length}"
end D71TesterT30

namespace D71TesterT31
-- B2 (iii): a closed map erase read at two value types (closedTwoTypes), then used
def two (n : Nat) : String :=
  let a := (({} : Std.HashMap Nat String).erase 3).insert n "a"
  let b := (({} : Std.HashMap Nat Nat).erase 3).insert n n
  s!"{a.size} {b.size} {a[n]?} {b[n]?} {a.contains 3}"
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println (two n)
  IO.println (two (n + 3))
end D71TesterT31

namespace D71TesterT33
structure Pkg where
  b : Bool
  v : if b then List Nat else List String
@[noinline] def ap (f : Pkg → Nat) (p : Pkg) : Nat := f p
@[noinline] def ap2 (f : Pkg → Nat) (p : Pkg) : Nat := ap f p + 1
@[noinline] def len : Pkg → Nat
  | ⟨true, v⟩ => let w : List Nat := v; w.foldl (· + ·) 0
  | ⟨false, v⟩ => let w : List String := v; w.length * 100
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let p1 : Pkg := ⟨true, (List.range n : List Nat)⟩
  let p2 : Pkg := ⟨false, (args : List String)⟩
  IO.println s!"{ap2 len p1} {ap2 len p2} {ap len p1}"
end D71TesterT33

namespace D71TesterT35
structure AnyT where
  {α : Type}
  [inst : ToString α]
  gen : Unit → α
@[noinline] def AnyT.force (s : AnyT) : String :=
  let t : Thunk s.α := Thunk.mk s.gen
  let k : Task s.α := Task.spawn s.gen
  s.inst.toString t.get ++ "/" ++ s.inst.toString k.get ++ "/" ++ s.inst.toString (s.gen ())
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let pre := s!"p{n}"
  let xs : List AnyT := [⟨fun _ => n * 2⟩, ⟨fun _ => pre ++ "!"⟩, ⟨fun _ => (n, decide (n > 1))⟩]
  IO.println (xs.map (·.force))
end D71TesterT35

namespace D71TesterT37
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
@[noinline] def getL {σ : Type} : FreeM (StateF σ) (List σ) := .liftBind .get fun a => .pure [a, a]
@[noinline] def getO {σ : Type} : FreeM (StateF σ) (Option σ) := .liftBind .get fun a => .pure (some a)
@[noinline] def getP {σ : Type} : FreeM (StateF σ) (σ × Nat) := .liftBind .get fun a => .pure (a, 5)
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println s!"{(run (getL (σ := Nat)) n).1} {(run (getL (σ := String)) "ab").1}"
  IO.println s!"{(run (getO (σ := Nat)) n).1} {(run (getO (σ := String)) "ab").1}"
  IO.println s!"{(run (getP (σ := Nat)) n).1} {(run (getP (σ := String)) "ab").1}"
end D71TesterT37

def main : IO Unit := do
  IO.println "-- D71TesterT27"
  D71TesterT27.caseMain ["4"]
  IO.println "-- D71TesterT28"
  D71TesterT28.caseMain ["2"]
  IO.println "-- D71TesterT28A"
  D71TesterT28A.caseMain []
  IO.println "-- D71TesterT28B"
  D71TesterT28B.caseMain []
  IO.println "-- D71TesterT28C"
  D71TesterT28C.caseMain ["2"]
  IO.println "-- D71TesterT29"
  D71TesterT29.caseMain ["4"]
  IO.println "-- D71TesterT30"
  D71TesterT30.caseMain ["3"]
  IO.println "-- D71TesterT31"
  D71TesterT31.caseMain ["4"]
  IO.println "-- D71TesterT33"
  D71TesterT33.caseMain ["a", "b"]
  IO.println "-- D71TesterT35"
  D71TesterT35.caseMain ["3"]
  IO.println "-- D71TesterT37"
  D71TesterT37.caseMain ["3"]
