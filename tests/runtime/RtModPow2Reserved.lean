/-! Runtime test (a refusal): the program defines `L2RNat.truncateBits`,
the name of the extern that the optimization `mod-pow2` adds for its
rewritten `x % 2 ^ w` (`l2r_nat_truncate_bits`). The `L2R*` namespaces
are lean2rr's: the pass must not call the program's definition in place
of the extern (it computes `x + w` here), so lean2rr ends with an internal
error that names the declaration and its module (before the check, the
pass reused the name and lean2rr failed later, calling it an unknown
extern of Lean's library). Natively the program is valid Lean. -/

def L2RNat.truncateBits (x w : Nat) : Nat := x + w

@[noinline] def modPow (x w : Nat) : Nat := x % 2 ^ w

def main (args : List String) : IO Unit := do
  let w := (args.head? >>= String.toNat?).getD 70
  IO.println s!"{modPow (2 ^ 80 + 5) w} {L2RNat.truncateBits 3 4}"
