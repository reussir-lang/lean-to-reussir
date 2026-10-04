/-! Runtime test: constructor names that render alike. `Weird.«a.b»` (one
name component containing a dot) and `Weird.a.b` (two components) are
different constructors; lean2rr must give them different variants. -/

inductive Weird where
  | «a.b» (n : Nat)
  | a.b (s : String)
  | c
  deriving Repr

def f : Weird → String
  | .«a.b» n => s!"esc {n}"
  | Weird.a.b s => s!"hier {s}"
  | .c => "c"

def main : IO Unit :=
  IO.println s!"{f (.«a.b» 3)} {f (Weird.a.b "x")} {f .c} {repr (Weird.a.b "y")} {repr (Weird.«a.b» 4)}"
