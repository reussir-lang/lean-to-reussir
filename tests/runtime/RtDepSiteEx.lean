/-! Runtime test: the program of the design site's page "Dependent types"
(docs/site/pages/dependent-types.md; all its examples in one program): a
polymorphic `pick`, a column whose element type is a field
(`Array ty.denote`), a type selected by a `Bool`, Sigma types, a type
stored in a field (`Pkg`), polymorphic recursion (`nest`), a structure field
that is a function over any element type (`Op.run`), and a shared tree
packed in an existential (`leftDepth ⟨Nat, build n⟩`). Natively, without
arguments, it prints the eight lines the page shows. -/
@[noinline] def pick (α : Type) (b : Bool) (x y : α) : α := if b then x else y

inductive Ty | nat | str

@[reducible] def Ty.denote : Ty → Type
  | .nat => Nat
  | .str => String

structure Column where
  ty : Ty
  data : Array ty.denote

@[noinline] def Column.push (c : Column) (i : Nat) : Column :=
  match c with
  | ⟨.nat, d⟩ => ⟨.nat, d.push i⟩
  | ⟨.str, d⟩ => ⟨.str, d.push (toString i)⟩

@[noinline] def pickT (b : Bool) : if b then Nat else String :=
  match b with
  | true => (42 : Nat)
  | false => "hello"

@[noinline] def describe : (b : Bool) → (if b then Nat else String) → String
  | true, n => let m : Nat := n; s!"nat {m + 1}"
  | false, s => let t : String := s; s!"str {t}"

@[noinline] def entries (n : Nat) : List ((t : Ty) × t.denote) :=
  [⟨.nat, n⟩, ⟨.str, toString n⟩]

structure Pkg where
  α : Type
  val : α
  fmt : α → String

@[noinline] def Pkg.show (p : Pkg) : String := p.fmt p.val

def nest {α : Type} [ToString α] : Nat → α → String
  | 0, x => toString x
  | n + 1, x => nest n (x, x)

structure Op where
  run : {α : Type} → List α → Nat

def ops : List Op := [⟨List.length⟩, ⟨fun xs => xs.length * 2⟩]

inductive Tree (α : Type) where
  | leaf (x : α)
  | node (left right : Tree α)

@[noinline] def build : Nat → Tree Nat
  | 0 => .leaf 7
  | n + 1 => let t := build n; .node t t

structure Packed where
  α : Type
  tree : Tree α

@[noinline] def leftDepth (p : Packed) : Nat := go p.tree
where
  go {α : Type} : Tree α → Nat
    | .leaf _ => 0
    | .node l _ => 1 + go l

def main (args : List String) : IO Unit := do
  let b := args.length == 0
  let n := args.length + 3
  IO.println (pick Nat b 1 2)
  let c := Column.push ⟨.nat, #[]⟩ n
  IO.println c.data.size
  IO.println (describe b (pickT b))
  IO.println (entries n).length
  IO.println (Pkg.show ⟨Nat, 5, toString⟩)
  IO.println (nest 2 n)
  IO.println (ops.map (fun o => o.run [1, 2, 3]))
  IO.println (leftDepth ⟨Nat, build n⟩)
