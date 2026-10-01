/-! Runtime test: a module compiled with `set_option compiler.extract_closed
false`: Lean extracts no closed terms, so closed terms in functions are
evaluated at each call and constants evaluate their own terms. -/
set_option compiler.extract_closed false

def t (s : String) (n : Nat) : Nat := dbgTrace s fun _ => n

def fx (n : Nat) : Nat := n + t "fx" 1
def fs (n : Nat) : String := toString n ++ "-" ++ toString (t "fs" 2)
def k1 : Nat := t "k1" 1
def k2 : Nat := t "k1" 1
def arr : Array Nat := #[t "a0" 0, t "a1" 1]
def fa (i : Nat) : Nat := #[t "fa0" 10, t "fa1" 11][i]!

def main : IO Unit := do
  IO.eprintln "main"
  IO.println s!"{fx 1} {fx 2} {fs 1} {fs 2} {k1} {k2} {arr} {fa 0} {fa 1}"
