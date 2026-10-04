/-! Runtime test: `Nat.pow` with an exponent above 2^32 - 1 is an internal
panic in Lean's runtime (`INTERNAL PANIC: Nat.pow exponent is too big`,
exit 1) — even for base 1; output printed before is flushed. lean2rr lifts
this limit where the result can be computed, as lean-runtime's rules do
(LB-11, translation plan §10, "Lean bugs we do not reproduce"): `1 ^ e` is 1
and the program goes on, so each side is compared with its own files
(RtInternalPanic.native.*, RtInternalPanic.l2r.*). RtLiftedLimits has an
exponent whose power cannot be computed, which ends as natively. -/

def main (args : List String) : IO Unit := do
  IO.println s!"small {(1 : Nat) ^ 4294967295} {(0 : Nat) <<< 18446744073709551616}"
  IO.println "before"
  let e : Nat := 4294967296 + args.length
  IO.println s!"huge {(1 : Nat) ^ e}"
  IO.println "after"
