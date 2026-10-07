/-! Runtime test: a function value that completes at an `lcAny` parameter
and is then applied where that parameter's type is erased (rule 4, the
flow of function values). `mkK p β b : p.α → β` is generic code at an
unknown type (`p.α` is a field of an existential: `lcAny` in mono code),
and runs its body when its `p.α` argument arrives. With `p := pT`, whose
`α` is `Type`, typed code sees the value at `Type → Nat → Nat`, where the
first domain is erased: it applies a type (`g Nat`) and then the result to
numbers. Natively `mkK` runs once, at `g Nat`. lean2rr keeps a unit domain
there because the value reaches that type: directly (an argument of type
`pT.α → Nat → Nat` passed for a parameter of type `Type → Nat → Nat`), and
through a `Box` (stored in an existential's field, read back by a cast into
a structure, so that Lean does not eta-expand the reader);
without it, `mkK` would run at each application of the result, and never
when the result is not applied. -/

structure Pkg where
  α : Type 1

@[noinline] def mkK (p : Pkg) (β : Type) (b : β) : p.α → β :=
  fun _ => dbgTrace "mkK" fun _ => b

def pT : Pkg := ⟨Type⟩

@[noinline] def loopN (h : Nat → Nat) (k : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:k] do acc := acc + h i
  return acc

-- Bound at a type once, applied `k` times.
@[noinline] def useK (g : Type → Nat → Nat) (k : Nat) : Nat := loopN (g Nat) k

-- Through a `Box`: an existential's field, read back at its type by a cast.
structure Dyn where
  τ : Type 1
  v : τ

@[noinline] def mkDyn (n : Nat) : Dyn := ⟨pT.α → Nat → Nat, mkK pT (Nat → Nat) (· * 3 + n)⟩
-- In a structure, so that Lean does not eta-expand `getF` (it would then
-- apply `d.v` at each application).
structure FnBox where
  f : Type → Nat → Nat
@[noinline] def getF (d : Dyn) (h : d.τ = (Type → Nat → Nat)) : FnBox := ⟨h ▸ d.v⟩

def main (args : List String) : IO Unit := do
  let n := args.length
  IO.println (useK (mkK pT (Nat → Nat) (· + n + 10)) 3)
  IO.println (useK (mkK pT (Nat → Nat) (· + n + 20)) 0)
  let d := mkDyn n
  IO.println (useK (getF d rfl).f 3)
  IO.println (useK (getF d rfl).f 0)
