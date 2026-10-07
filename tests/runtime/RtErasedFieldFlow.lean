/-! Runtime test (review of rule 4's flow analysis, repro A1): a function
value that completes at an `lcAny` parameter (`mkK p β b : p.α → β`, generic
over an existential's type field) is stored in a structure whose type
argument mentions no function type (`Op3 p.α`), and read at an instance
where that domain is erased (`Op3 Type`: `run : Type → Nat → Nat`). Stage 4
converts the structure field by field between the two instances, so the
value reaches `Type → Nat → Nat`: the flow analysis links the fields of the
two instances, and the type keeps a unit domain there. Natively `mkK` runs
once per `o.run Nat` (also when the result is applied 0 times); without the
link it ran at each application of the result. -/
structure Pkg where
  α : Type 1

structure Op3 (α : Type 1) where
  tag : Nat
  run : α → Nat → Nat

@[noinline] def mkK (p : Pkg) (β : Type) (b : β) : p.α → β :=
  fun _ => dbgTrace "mkK" fun _ => b

def pT : Pkg := ⟨Type⟩

@[noinline] def mkOp (p : Pkg) (n : Nat) : Op3 p.α := ⟨n, mkK p (Nat → Nat) (· + n)⟩

@[noinline] def loopN (h : Nat → Nat) (k : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:k] do acc := acc + h i
  return acc

@[noinline] def useOp (o : Op3 Type) (k : Nat) : Nat := loopN (o.run Nat) k

def main (args : List String) : IO Unit := do
  let n := args.length
  IO.println (useOp (mkOp pT n) 3)
  IO.println (useOp (mkOp pT (n+1)) 0)
