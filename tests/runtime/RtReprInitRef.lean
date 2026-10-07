/-! Runtime test: `initialize` constants holding a reference and a list
(design review of the layout redesign, correctness, DRC-01). The
initializers' results reach the program through the startup glue, which
the translation's type rules do not see: their layouts must stay those the
glue expects (a reference cell of `Nat`, a `List Nat`). -/
initialize counter : IO.Ref Nat ← IO.mkRef 5
initialize table : List Nat ← pure [1, 2, 3]

@[noinline] def bump : IO Nat := do
  counter.modify (· + 1)
  counter.get

def main : IO Unit := do
  let a ← bump
  let b ← bump
  IO.println s!"{a} {b} {table.length} {table}"
