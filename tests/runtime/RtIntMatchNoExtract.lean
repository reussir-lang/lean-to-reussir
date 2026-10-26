/-! Runtime test: `Int` literal matches when Lean extracts no closed term
(`compiler.extract_closed false`), so a negative literal is computed in
place (`Int.neg (Int.ofNat 6)`) and CSE lets an arm return the literal it
was tested against. With optimization `int-match` (on by default,
Lower/IntMatch) the tests are one `match`; an arm that keeps such a
literal must keep the `let`s it reads too (review of 762c2ac6: the arm kept
`Int.neg b` but dropped `b := Int.ofNat a` and `a := 6`, and lean2rr
stopped with "unbound variable (internal error)"). Shapes: arms returning
their literal (`f`), the default and later arms reading literals of earlier
tests (`g`), literal tests then the `Int` split with nested fields (`h`);
small values of both signs and ±2^70, computed at run time. Every line
must equal native Lean's. -/

set_option compiler.extract_closed false

/-- Int literal arms returning their literal (in place: Int.neg (Int.ofNat 6)). -/
def f (i : Int) : Int := match i with
  | 3 => 30
  | 5 => 5
  | -6 => -6
  | _ => 0

/-- Default and later arms reading literals of earlier tests. -/
def g (i : Int) : List Int := match i with
  | 2 => [2, 7]
  | -7 => [7, -7, 2]
  | 9 => [-7, 9]
  | _ => [i, -7, 9]

/-- Literal tests then the Int split with nested fields. -/
def h (i : Int) : Int := match i with
  | 5 => 5
  | -4 => -4
  | .ofNat 0 => 100
  | .ofNat (n+1) => n - 4
  | .negSucc 0 => -1
  | .negSucc (m+1) => -(m : Int) - 5

def main (args : List String) : IO Unit := do
  let b : Int := args.length
  let xs : List Int := [b, b+2, b+3, b+5, b-6, b-7, b+7, b+8, b+9, b-4, b-1, b-2, b - 100, 2^(70 + args.length), -(2^(70 + args.length))]
  IO.println s!"{xs.map f}"
  IO.println s!"{xs.map g}"
  IO.println s!"{xs.map h}"
