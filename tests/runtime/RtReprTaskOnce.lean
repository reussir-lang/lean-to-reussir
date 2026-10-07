/-! Runtime test (blowup audit, semantics probe SemTaskOnce): a task reached
through a typed view and through existential packages (`Task (List α)`) runs
once (one "run" trace), and an `IO.asTask` whose action counts its runs in a
reference runs once. -/
structure PkK where
  α : Type
  t : Task (List α)

@[noinline] def waitU (p : PkK) : Nat := p.t.get.length
@[noinline] def waitU2 (p q : PkK) : Nat := p.t.get.length + q.t.get.length

@[noinline] def mk (tag : String) (n : Nat) : Task (List Nat) :=
  Task.spawn fun _ => dbgTrace s!"run {tag}" fun _ => List.range n

def main : IO Unit := do
  let t := mk "a" 5
  IO.println s!"a uniform {waitU ⟨Nat, t⟩}"
  IO.println s!"a typed {t.get.length}"
  IO.println s!"a two packages {waitU2 ⟨Nat, t⟩ ⟨Nat, t⟩}"
  let runs ← IO.mkRef 0
  let k ← IO.asTask (do runs.modify (· + 1); return List.range 4)
  let k' : Task (List Nat) := k.map fun | .ok l => l | .error _ => []
  IO.println s!"b uniform {waitU ⟨Nat, k'⟩} {waitU ⟨Nat, k'⟩}"
  IO.println s!"b typed {k'.get.length}"
  IO.println s!"b runs {← runs.get}"
