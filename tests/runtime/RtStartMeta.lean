module

/-! Runtime test: a `module` main initializes only its runtime phase
(translation plan §5.12): `meta initialize` actions and constants and
`meta def` constants are compile-time only and do not run, so the first
one's error does not stop the program. A specialization made while
compiling a `meta def` is not marked `meta`: natively it runs with the
runtime phase. -/

def t (s : String) (n : Nat) : Nat := dbgTrace s fun _ => n

@[specialize] meta def gen {m : Type → Type} [Monad m] (f : Nat → m Nat) : m Nat := f 1

meta initialize do throw (IO.userError "meta initialize ran")
meta initialize metaRef : IO.Ref Nat ← do IO.eprintln "meta initialize constant"; IO.mkRef 0
meta def metaConst : Nat := dbgTrace "meta constant" fun _ => 1
def rtConst : Nat := t "rtConst" 2
initialize rtRef : IO.Ref Nat ← do IO.eprintln "initialize constant"; IO.mkRef 7
meta def metaConst2 : List Nat := [dbgTrace "meta constant 2" fun _ => 3]
meta def metaSpec : Nat :=
  Id.run (gen (m := Id) (fun i => dbgTrace "specialization made in a meta def" fun _ => pure (i + 1)))
initialize do IO.eprintln "initialize action"
def rtConst2 : Nat := t "rtConst2" (rtConst + 1)
meta initialize do IO.eprintln "meta initialize action"

public def main : IO Unit := do
  IO.println s!"main {rtConst} {rtConst2} {← rtRef.get}"
