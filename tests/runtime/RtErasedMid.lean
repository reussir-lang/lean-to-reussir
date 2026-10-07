/-! Runtime test: type arguments in the middle and at the end of parameter
lists (rule 4). lean2rr removes an erased parameter unless it is the last
one; a call drops the `◾` arguments of removed parameters; a partial
application stops at any Lean position, also between a type argument and
the data after it; an over-application applies the function's result to
the rest, along the result type's Lean positions. Values of the same type
can differ in where they run (`mkF` runs at the type, `mid3 1 Nat 2` at
the data after it): a unit kept for one is ignored by the other. The
traces show when each body runs and how many times. -/

universe u
@[noinline] def mid3 (x : Nat) (_ : Type) (y : Nat) (_ : Type) (z : Nat) : Nat :=
  dbgTrace s!"mid3 {x} {y} {z}" fun _ => x * 100 + y * 10 + z
@[noinline] def endT (x y : Nat) (_ _ : Type) : Nat := dbgTrace s!"endT {x} {y}" fun _ => x * y
@[noinline] def mkF {β : Type u} (n : Nat) (b : β) : (α : Type) → β :=
  fun _ => dbgTrace s!"mkF {n}" fun _ => b

@[noinline] def ap1 (p : (α : Type) → Nat → (β : Type) → Nat → Nat) (k : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:k] do acc := acc + p Nat i String (i + 1)
  return acc
@[noinline] def ap2 (p : Nat → (β : Type) → Nat → Nat) (k : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:k] do acc := acc + p i String i
  return acc
@[noinline] def ap3 (p : (β : Type) → Nat → Nat) (k : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:k] do acc := acc + p Bool i
  return acc
@[noinline] def ap4 (p : Nat → Nat) (k : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:k] do acc := acc + p i
  return acc
-- Staged: bound at the type once, then applied.
@[noinline] def ap3s (p : (β : Type) → Nat → Nat) (k : Nat) : Nat := ap4 (p Bool) k
@[noinline] def apE (p : (α β : Type) → Nat) (k : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:k] do acc := acc + p Nat String
  return acc

-- An over-application of `mkF` (arity 3) to 6 arguments.
@[noinline] def over (k : Nat) : Nat :=
  @mkF (Nat → (β : Type) → Nat) k (fun n _ => dbgTrace s!"inner {n}" fun _ => n + k) Nat (k + 1) String

def main : IO Unit := do
  IO.println (mid3 1 Nat 2 String 3 + endT 4 5 Nat Bool)
  IO.println (ap1 (mid3 1) 2)
  IO.println (ap2 (@mid3 2 Nat) 2)
  IO.println (ap3 (mid3 3 Nat 4) 2)
  IO.println (ap3 (mkF 9 (fun i => i + 1000)) 2)
  IO.println (ap3s (mid3 4 Nat 5) 2)
  IO.println (ap3s (mkF 8 (fun i => i + 2000)) 2)
  IO.println (ap3s (mid3 5 Nat 6) 0)
  IO.println (ap4 (mid3 6 Nat 7 Nat) 2)
  IO.println (apE (endT 7 8) 2)
  IO.println (apE (endT 9 9) 0)
  IO.println (over 3)
