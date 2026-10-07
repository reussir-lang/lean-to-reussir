/-! Runtime test (blowup audit, semantics probe SemThunkOnce): a thunk
reached through a typed view and through existential packages (uniform code,
`Thunk (List α)`) is evaluated once (one "eval" trace on stderr), whichever
view forces it first, and also when two packages of the same pending thunk
are both forced. -/
structure PkT where
  α : Type
  t : Thunk (List α)

@[noinline] def forceU (p : PkT) : Nat := p.t.get.length
@[noinline] def forceU2 (p q : PkT) : Nat := p.t.get.length + q.t.get.length

@[noinline] def mk (tag : String) (n : Nat) : Thunk (List Nat) :=
  Thunk.mk fun _ => dbgTrace s!"eval {tag}" fun _ => List.range n

def main : IO Unit := do
  -- uniform first, then typed, then uniform again
  let t := mk "a" 5
  IO.println s!"a uniform {forceU ⟨Nat, t⟩}"
  IO.println s!"a typed {t.get.length}"
  IO.println s!"a uniform again {forceU ⟨Nat, t⟩}"
  -- typed first
  let u := mk "b" 6
  IO.println s!"b typed {u.get.length}"
  IO.println s!"b uniform {forceU ⟨Nat, u⟩}"
  -- two packages of one pending thunk, both forced in uniform code
  let w := mk "c" 7
  IO.println s!"c two packages {forceU2 ⟨Nat, w⟩ ⟨Nat, w⟩}"
  IO.println s!"c typed {w.get.length}"
