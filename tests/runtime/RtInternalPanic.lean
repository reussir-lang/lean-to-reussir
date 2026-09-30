/-! Runtime test: `Nat.pow` with an exponent above 2^32 - 1 is an internal
panic in Lean's runtime (`INTERNAL PANIC: Nat.pow exponent is too big`,
exit 1) — even for base 1. Output printed before is flushed. -/

def main (args : List String) : IO Unit := do
  IO.println s!"small {(1 : Nat) ^ 4294967295} {(0 : Nat) <<< 18446744073709551616}"
  IO.println "before"
  let e : Nat := 4294967296 + args.length
  IO.println s!"huge {(1 : Nat) ^ e}"
  IO.println "after"
