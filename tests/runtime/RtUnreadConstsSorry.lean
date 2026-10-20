/-! Runtime test of the optimization `unread-consts` (hunt r7 B): an unread
constant whose code is only `unreach` (`False.elim` of a proof made with
`sorry`). Natively the module's initializer evaluates it before `main` and
reaches `lean_internal_panic_unreachable`: the program prints `INTERNAL
PANIC: unreachable code has been reached` and exits with code 1. The pass
took `unreach` as code that never runs and left the constant out, so
lean2rr's program printed `main ran`. A constant whose declaration rests on
`sorry` (or an axiom that is not standard) now stays. -/

theorem bogus : False := sorry

def bad : Nat := False.elim bogus

def main : IO Unit := IO.println "main ran"
