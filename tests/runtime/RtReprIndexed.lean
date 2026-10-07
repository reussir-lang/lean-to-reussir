/-! Runtime test (blowup audit, semantics probe SemIndexed): (1) An indexed
family `Expr : Ty → Type` (the index is erased, one layout) evaluated by a
function with a dependent result (`eval : Expr t → t.denote`), packed into
`(t : Ty) × Expr t` and kept in a list; a shared expression DAG (N levels)
is packed and only its root is inspected: no conversion is expected
(allocations must not grow exponentially with N). (2) A structure whose
field is data at one instantiation and a proof at another (`Wrap (α : Sort
u)`: `val : α` with `α := Nat` and `α := (k < 5)`), handled by one generic
function at both; results must equal native. The argument is N (default 10).
The output is checked here; the allocations by tests/runtime/alloc-check.sh
(RtReprIndexed.alloc), for N = 10 and 20. -/
inductive Ty | nat | bool

@[reducible] def Ty.denote : Ty → Type
  | .nat => Nat
  | .bool => Bool

inductive Expr : Ty → Type where
  | lit (n : Nat) : Expr .nat
  | add (a b : Expr .nat) : Expr .nat
  | lt (a b : Expr .nat) : Expr .bool
  | ite {t : Ty} (c : Expr .bool) (a b : Expr t) : Expr t

def eval : {t : Ty} → Expr t → t.denote
  | _, .lit n => n
  | _, .add a b => (eval a : Nat) + eval b
  | _, .lt a b => decide ((eval a : Nat) < eval b)
  | _, .ite c a b => if eval c then eval a else eval b

@[noinline] def dag : Nat → Expr .nat
  | 0 => .lit 1
  | n + 1 => let e := dag n; .add e e

@[noinline] def rootKind (p : (t : Ty) × Expr t) : String :=
  match p with
  | ⟨_, .lit _⟩ => "lit"
  | ⟨_, .add _ _⟩ => "add"
  | ⟨_, .lt _ _⟩ => "lt"
  | ⟨_, .ite _ _ _⟩ => "ite"

@[noinline] def evalSmall (p : (t : Ty) × Expr t) : String :=
  match p with
  | ⟨.nat, e⟩ => s!"nat {eval e}"
  | ⟨.bool, e⟩ => s!"bool {eval e}"

structure Wrap (α : Sort u) where
  val : α
  tag : Nat

inductive WL (α : Sort u) where
  | nil
  | cons (w : Wrap α) (r : WL α)

@[noinline] def sumTags {α : Sort u} : WL α → Nat
  | .nil => 0
  | .cons w ws => w.tag + sumTags ws

@[noinline] def vals : WL Nat → Nat
  | .nil => 0
  | .cons w ws => w.val + vals ws

def mkWL {α : Sort u} (f : Nat → Wrap α) : Nat → WL α
  | 0 => .nil
  | k + 1 => .cons (f k) (mkWL f k)

def main (args : List String) : IO Unit := do
  let n := (args.headD "10").toNat!
  let small : List ((t : Ty) × Expr t) :=
    [⟨.nat, .add (.lit 2) (.lit 3)⟩, ⟨.bool, .lt (.lit 2) (.lit 3)⟩,
     ⟨.nat, .ite (.lt (.lit 5) (.lit 1)) (.lit 7) (.lit 8)⟩]
  IO.println (small.map evalSmall)
  let big : (t : Ty) × Expr t := ⟨.nat, dag n⟩
  IO.println s!"{rootKind big} {small.map rootKind}"
  let ds : WL Nat := mkWL (fun i => ⟨i * 10, i⟩) 5
  let ps : WL (3 < 5) := mkWL (fun i => ⟨by decide, i + 1⟩) 5
  IO.println s!"{sumTags ds} {sumTags ps} {vals ds}"
