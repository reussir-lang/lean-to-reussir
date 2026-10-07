/-! Runtime test (review of rule 4's flow analysis, repro A5): as
`RtErasedFieldFlow` with a proof domain: universe-generic existential code
builds `Op3 p.α` (the domain is `lcAny`), typed code reads `Op3 True` (the
domain is a proof, erased) and applies `o.run trivial`. Natively `mkK` runs
once per `o.run trivial`. -/
universe u
structure Pkg where
  α : Sort u

structure Op3 (α : Sort u) where
  tag : Nat
  run : α → Nat → Nat

@[noinline] def mkK (p : Pkg.{u}) (β : Type) (b : β) : p.α → β :=
  fun _ => dbgTrace "mkK" fun _ => b

def pT : Pkg.{0} := ⟨True⟩

@[noinline] def mkOp (p : Pkg.{u}) (n : Nat) : Op3 p.α := ⟨n, mkK p (Nat → Nat) (· + n)⟩

@[noinline] def loopN (h : Nat → Nat) (k : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:k] do acc := acc + h i
  return acc

@[noinline] def useOp (o : Op3 True) (k : Nat) : Nat := loopN (o.run trivial) k

def main (args : List String) : IO Unit := do
  let n := args.length
  IO.println (useOp (mkOp pT n) 3)
  IO.println (useOp (mkOp pT (n+1)) 0)
