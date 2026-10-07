/-! Runtime test (review of rule 4's flow analysis, repro A2): as
`RtErasedFieldFlow`, through a `Box`: the structure `Op3 p.α`, whose type
argument mentions no function type, is stored in an existential's field
and read back at `Op3 Type` by a cast. The analysis counts a structure
whose fields can hold a function value (`mayHoldFn`) as a boxed type, and
links the fields of the two instances that meet through the `Box`. Natively
`mkK` runs once per `o.run Nat`. -/
structure Pkg where
  α : Type 1

structure Op3 (α : Type 1) where
  tag : Nat
  run : α → Nat → Nat

@[noinline] def mkK (p : Pkg) (β : Type) (b : β) : p.α → β :=
  fun _ => dbgTrace "mkK" fun _ => b

def pT : Pkg := ⟨Type⟩

@[noinline] def mkOp (p : Pkg) (n : Nat) : Op3 p.α := ⟨n, mkK p (Nat → Nat) (· + n)⟩

structure Dyn where
  τ : Type 1
  v : τ

@[noinline] def mkDyn (n : Nat) : Dyn := ⟨Op3 pT.α, mkOp pT n⟩
@[noinline] def getOp (d : Dyn) (h : d.τ = Op3 Type) : Op3 Type := h ▸ d.v

@[noinline] def loopN (h : Nat → Nat) (k : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:k] do acc := acc + h i
  return acc

@[noinline] def useOp (o : Op3 Type) (k : Nat) : Nat := loopN (o.run Nat) k

def main (args : List String) : IO Unit := do
  let n := args.length
  IO.println (useOp (getOp (mkDyn n) rfl) 3)
  IO.println (useOp (getOp (mkDyn (n+1)) rfl) 0)
