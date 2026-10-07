/-! Runtime test: one generic function (`Tree.size`) used at two element
types (`Tree Float`, `Tree String`), the specialization example of the
design site's page "Dependent types". -/
inductive Tree (α : Type) where
  | leaf (x : α)
  | node (left right : Tree α)

@[noinline] def Tree.size {α : Type} : Tree α → Nat
  | .leaf _ => 1
  | .node l r => l.size + r.size

def main : IO Unit := do
  let a : Tree Float := .node (.leaf 1.5) (.leaf 2.5)
  let b : Tree String := .node (.leaf "x") (.leaf "y")
  IO.println (a.size + b.size)
