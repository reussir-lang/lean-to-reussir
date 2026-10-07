/-! Runtime test: case `D71BreakerP09A` of the shared dependent-type corpus
(programs built by another translator's team and checked against native
Lean). It checks: Scalar casts only (Nat as Bool, Bool as Nat, UInt64 bits)
-/
/- P09A: scalar casts only (Nat as Bool, Bool as Nat, UInt64 bits) -/
unsafe def castNatBool (n : Nat) : Bool := unsafeCast n
@[implemented_by castNatBool] def natBool (n : Nat) : Bool := n != 0
unsafe def castBoolNat (b : Bool) : Nat := unsafeCast b
@[implemented_by castBoolNat] def boolNat (b : Bool) : Nat := if b then 1 else 0
def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println s!"{natBool (n % 2)} {natBool 0} {boolNat (n > 2)} {boolNat false}"
