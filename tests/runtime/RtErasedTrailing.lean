/-! Runtime test: functions whose last parameters are erased (rule 4, map C
hazard H2): a type or a proof after the data. lean2rr keeps one unit
parameter for the trailing erased ones, so that `f 3` stays a partial
application: the body runs when the last (erased) argument is applied, as
in Lean, not when the data is. The traces show when each body runs and how
many times: a partial application applied in a loop of its own (Lean's
`cse` merges two applications to types or proofs), and one never
applied. -/

@[noinline] def f (x : Nat) (_ : Type) : Nat := dbgTrace s!"f {x}" fun _ => x + 1
@[noinline] def g (x : Nat) (_ : x > 0) : Nat := dbgTrace s!"g {x}" fun _ => x * 2
-- Two trailing erased parameters: one unit parameter for both.
@[noinline] def h (x y : Nat) (_ : Type) (_ : x + y > 0) : Nat := dbgTrace s!"h {x} {y}" fun _ => x + y

@[noinline] def loopTy (p : (α : Type) → Nat) (k : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:k] do acc := acc + p Nat
  return acc

@[noinline] def loopPf (n : Nat) (p : n > 0 → Nat) (pf : n > 0) (k : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:k] do acc := acc + p pf
  return acc

@[noinline] def loopTyPf (p : (α : Type) → 1 + 2 > 0 → Nat) (k : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:k] do acc := acc + p Nat (by decide)
  return acc

-- A partial application made in a loop and never applied.
@[noinline] def keep (p : (α : Type) → Nat) : List ((α : Type) → Nat) := [p, p]
@[noinline] def buildMany (k : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:k] do acc := acc + (keep (f i)).length
  return acc

-- `Array.mapFinIdx`'s function takes a proof last: `(i : Nat) → α → i < n → β`.
@[noinline] def label (xs : Array String) : Array String :=
  xs.mapFinIdx fun i x _ => dbgTrace s!"label {i}" fun _ => s!"{i}:{x}"

-- `List.pmap`'s function takes a proof last.
@[noinline] def halves (xs : List Nat) (h : ∀ x ∈ xs, x > 0) : List Nat :=
  xs.pmap (fun x (_ : x > 0) => dbgTrace s!"half {x}" fun _ => x / 2) h

def main : IO Unit := do
  IO.println (loopTy (f 3) 2)
  IO.println (loopTy (f 4) 0)
  IO.println (loopPf 5 (g 5) (by decide) 2)
  IO.println (loopPf 6 (g 6) (by decide) 0)
  IO.println (loopTyPf (h 1 2) 2)
  IO.println (loopTyPf (h 2 1) 0)
  IO.println (loopTy (Function.const Type (dbgTrace "const" fun _ => 9)) 2)
  IO.println (buildMany 3)
  IO.println (label #["a", "b", "c"])
  IO.println (halves [2, 4, 6] (by decide))
