/-! Runtime test: startup order of hand-written `@[init f]` declarations
whose function `f` is an ordinary declaration defined earlier: natively the
constant is initialized at its own place (Lean compiled `f` before), unlike
the function `initialize` makes, which belongs to its constant. -/

def t (s : String) (n : Nat) : Nat := dbgTrace s fun _ => n

def mkZ : IO Nat := do IO.eprintln "mkZ"; pure 1
def mkA : IO Nat := do IO.eprintln "mkA"; pure 2
def runQ : IO Unit := IO.eprintln "runQ"

def a0 : Nat := t "a0" 0
@[init mkZ] opaque zc : Nat
def a1 : Nat := t "a1" zc
@[init mkA] opaque ac : Nat
@[init] def runP : IO Unit := IO.eprintln "runP"
def a2 : Nat := t "a2" ac
@[init runQ] opaque unitC : Unit
initialize gen : Nat ← do IO.eprintln "gen (initialize)"; pure 3
def a3 : Nat := t "a3" gen

def main : IO Unit := do
  IO.eprintln "main"
  IO.println s!"{a0} {a1} {a2} {a3}"
