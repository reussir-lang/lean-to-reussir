/-! Runtime test: the program defines `L2RNat.truncateBits`, the name of
the extern that the optimization `mod-pow2` adds for its rewritten
`x % 2 ^ w` (`l2r_nat_truncate_bits`) had. The pass must not call the
program's definition in place of the extern (it computes `x + w` here),
nor the program's calls the extern. Before the check, the pass reused the
name and lean2rr failed later, calling it an unknown extern of Lean's
library; then lean2rr refused the program (the `L2R*` namespaces were
lean2rr's). Since a bug hunt of the names lean2rr recognizes (2026-10-27)
the extern is `L2RNat.truncateBits.0`, a name no program can declare (a
number as its last part), and the program runs as natively. -/

def L2RNat.truncateBits (x w : Nat) : Nat := x + w

@[noinline] def modPow (x w : Nat) : Nat := x % 2 ^ w

def main (args : List String) : IO Unit := do
  let w := (args.head? >>= String.toNat?).getD 70
  IO.println s!"{modPow (2 ^ 80 + 5) w} {L2RNat.truncateBits 3 4}"
