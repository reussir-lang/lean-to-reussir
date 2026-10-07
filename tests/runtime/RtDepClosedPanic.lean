/-! Runtime test: a closed term whose callee traces and panics inside
(design review of the layout redesign, correctness, DRC2-01). Lean
extracts `mayPanic []` from `useIt` (it checks `@[never_extract]` only on
the direct callee) and evaluates it once, at initialization: natively
"evaluated" and the panic print once, although `useIt` runs twice. A copy
of the term for each representation would print them twice. -/
@[noinline] def mayPanic (xs : List Nat) : List Nat :=
  dbgTrace "evaluated" fun _ => [xs.head!, 2, 3]

@[noinline] def useIt (n : Nat) : Nat := n + (mayPanic []).length

def main (args : List String) : IO Unit := do
  let k := (args.headD "2").toNat!
  IO.println s!"{useIt k} {useIt (k + 1)}"
