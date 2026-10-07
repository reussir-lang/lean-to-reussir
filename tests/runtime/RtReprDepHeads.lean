/-! Runtime test: one position of unknown type (a dependent result,
`t.denote`) reached by values of two different heads (`List Nat` and
`Option String`), and one dependent parameter used at those two types in
branches that never both run (design review of the layout redesign,
correctness, DRC-02): a rule that joined the two heads into one layout
would be wrong for one of them. -/
inductive Ty | nat | str
abbrev Ty.denote : Ty → Type
  | .nat => List Nat
  | .str => Option String

@[noinline] def mk (t : Ty) (n : Nat) : t.denote :=
  match t with
  | .nat => [n, n + 1]
  | .str => some (toString n)

@[noinline] def strLen (s : Option String) : Nat := (s.getD "").length
@[noinline] def sumL (xs : List Nat) : Nat := xs.foldl (· + ·) 0

@[noinline] def use (t : Ty) (x : t.denote) : Nat :=
  match t, x with
  | .nat, xs => sumL xs
  | .str, s => strLen s

def main (args : List String) : IO Unit := do
  let n := (args.headD "3").toNat!
  IO.println s!"{use .nat (mk .nat n)} {use .str (mk .str n)}"
