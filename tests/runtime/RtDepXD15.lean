/-! Runtime test: cases of the shared dependent-type corpus (programs built
by another translator's team and checked against native Lean), combined:
each case keeps its code in a namespace named after its case id, and `main`
runs each with that case's arguments in this order, printing `-- <id>`
before it (and `exit <code>` after a `main : IO UInt32`). The cases, with
what each checks:
- `D71TesterT38`: The source of a conversion kept and used after the
  crossing (aliasing), a list and a tree
- `D71TesterT39`: B7 Array conversion where the program itself calls the
  array primitives (getInternal, push, size)
- `D71TesterT41A`: B2 (iii) arrow domain: a shared value whose class reaches
  an arrow's domain (getK-like reader/writer, a callback result in a
  structure)
- `D71TesterT41B`: B2 (iii) arrow domain: a shared value whose class reaches
  an arrow's domain (getK-like reader/writer, a callback result in a
  structure)
- `D71TesterX66`: (iii): a shared closed term `@swapK ◾ : FreeM (StateF
  lcAny) (σ × σ)`, read at σ := Nat and σ := String, whose result pair holds
  the state the continuation's parameter brings back (a ... -/

namespace D71TesterT38
inductive Tree (α : Type) where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α
structure Pkg where
  b : Bool
  v : if b then List Nat × Tree Nat else List String × Tree String
@[noinline] def mkL (n : Nat) : List Nat := List.range n
@[noinline] def mkT (n : Nat) : Tree Nat := if n = 0 then .leaf 0 else let t := mkT (n - 1); .node t (.leaf n)
@[noinline] def tsum : Tree Nat → Nat
  | .leaf x => x
  | .node l r => tsum l + tsum r
@[noinline] def rd : Pkg → String
  | ⟨true, v⟩ => let w : List Nat × Tree Nat := v; s!"{w.1.length}/{tsum w.2}"
  | ⟨false, v⟩ => let w : List String × Tree String := v; s!"{w.1}"
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let l := mkL n
  let t := mkT n
  let p : Pkg := ⟨true, (l, t)⟩
  let q : Pkg := ⟨false, (args, .leaf "x")⟩
  let l2 := l ++ [100]
  IO.println s!"{rd p} {rd q} {l2} {tsum t} {l.length}"
end D71TesterT38

namespace D71TesterT39
structure Pkg where
  b : Bool
  v : if b then Array Nat else Array String
@[noinline] def mkA (n : Nat) : Array Nat := Id.run do
  let mut a := #[]
  for i in [0:n] do a := a.push i
  return a
@[noinline] def mkN (n : Nat) : Pkg := ⟨true, mkA n⟩
@[noinline] def mkS (n : Nat) : Pkg := ⟨false, (mkA n).map toString⟩
@[noinline] def get0 (xs : Array Nat) (i : Nat) : Nat := xs[i]!
@[noinline] def rd : Pkg → String
  | ⟨true, v⟩ => let w : Array Nat := v; toString (get0 w 0 + w.size)
  | ⟨false, v⟩ => let w : Array String := v; s!"{w.size}:{w}"
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  IO.println s!"{[mkN n, mkS n, mkN 1].map rd}"
end D71TesterT39

namespace D71TesterT41A
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
  .liftBind .get fun a => .liftBind .get fun b => .pure (a, b)
structure Tw (σ : Type) where
  run : (Nat → σ) → Nat → List σ
@[noinline] def tw {σ : Type} : Tw σ := ⟨fun f n => (List.range n).map f⟩
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println s!"{run (swapK (σ := Nat)) n} {run (swapK (σ := String)) "ab"}"
end D71TesterT41A

namespace D71TesterT41B
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
@[noinline] def swapK {σ : Type} : FreeM (StateF σ) σ :=
  .liftBind .get fun a => .liftBind (.set a) fun _ => .liftBind .get fun b => .pure b
structure Tw (σ : Type) where
  run : (Nat → σ) → Nat → List σ
@[noinline] def tw {σ : Type} : Tw σ := ⟨fun f n => (List.range n).map f⟩
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println s!"{run (swapK (σ := Nat)) n} {run (swapK (σ := String)) "ab"}"
end D71TesterT41B

namespace D71TesterX66

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
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println s!"{run (swapK (σ := Nat)) n} {run (swapK (σ := String)) "ab"}"
end D71TesterX66

def main : IO Unit := do
  IO.println "-- D71TesterT38"
  D71TesterT38.caseMain ["3"]
  IO.println "-- D71TesterT39"
  D71TesterT39.caseMain ["3"]
  IO.println "-- D71TesterT41A"
  D71TesterT41A.caseMain ["2"]
  IO.println "-- D71TesterT41B"
  D71TesterT41B.caseMain ["2"]
  IO.println "-- D71TesterX66"
  D71TesterX66.caseMain []
