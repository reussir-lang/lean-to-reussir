/-! Runtime test: case splits on `Int`, which under `--int-backend rcgmp`
are Reussir `match`es on the built-in integer (optimization `int-match`,
Lower/IntMatch): `ofNat` and `negSucc` (`Int::OfNat(m)`, whose binder is
the scrutinee itself, and `Int::NegSucc(m)`, whose binder is `-i - 1`),
splits of the field fused into one match (`0`, `ofNat (n+1)`, `-1`,
`negSucc (m+1)`), a default beside `ofNat 0`, `Int` literal patterns, the
scrutinee named in each kind of arm, `Int.repr`, `Int.toNat`
and `Int.natAbs` (Lean's own splits), and a sign split in a loop. Inputs:
small values of both signs, the edges of rcgmp's immediates (±2^61 and
their neighbours, -2^61 - 1 is the first negative heap value), and heap
values (±2^63, ±2^64, ±10^30), some computed at run time from the number
of arguments. Every line must equal native Lean's, under both
representations. -/

def sign : Int → Int
  | .ofNat 0 => 0
  | .ofNat (_+1) => 1
  | .negSucc _ => -1

def parts : Int → String
  | .ofNat n => s!"ofNat {n}"
  | .negSucc m => s!"negSucc {m}"

/-- The fields' own splits, fused into one match. -/
def fine : Int → Nat
  | .ofNat 0 => 1000
  | .ofNat (n+1) => n
  | .negSucc 0 => 2000
  | .negSucc (m+1) => m + 3000

/-- The scrutinee named in every arm. -/
def named : Int → Int
  | .ofNat n => n + 2 * (.ofNat n : Int)
  | .negSucc m => 10 * (.negSucc m : Int) + m

def namedI (i : Int) : Int :=
  match i with
  | .ofNat n => i + n
  | .negSucc m => i * 3 + m

/-- A default beside `ofNat 0`. -/
def ofNatOr : Int → Int
  | .ofNat 0 => 100
  | i => i * 2

/-- `Int` literals (Lean tests them, or splits `ofNat`/`negSucc`). -/
def intLit (i : Int) : String :=
  match i with
  | 0 => "zero"
  | 1 => "one"
  | -1 => "minus one"
  | 5 => "five"
  | -7 => "minus seven"
  | _ => "other"

/-- A sign split in a loop: the sum of |i| for i from `lo` to `hi`. -/
def absSum (lo : Int) : Nat → Int → Int
  | 0, acc => acc
  | k+1, acc =>
    let i := lo + k
    absSum lo k (acc + match i with
      | .ofNat n => n
      | .negSucc m => m + 1)

def main (args : List String) : IO Unit := do
  let b : Int := args.length
  let p61 : Int := 2 ^ (61 + args.length)
  let small : List Int := [b, b + 1, b + 2, b - 1, b - 2, b - 3, b + 100, b - 100]
  let big : List Int := [p61 - 1, p61, p61 + 1, -p61 + 1, -p61, -p61 - 1, -p61 - 2,
    2 ^ (63 + args.length), -2 ^ (63 + args.length), 2 ^ (64 + args.length),
    -2 ^ (64 + args.length), 10 ^ (30 + args.length), -10 ^ (30 + args.length)]
  let all := small ++ big
  IO.println s!"sign {all.map sign}"
  IO.println s!"parts {all.map parts}"
  IO.println s!"fine {all.map fine}"
  IO.println s!"named {all.map named}"
  IO.println s!"namedI {all.map namedI}"
  IO.println s!"ofNatOr {all.map ofNatOr}"
  IO.println s!"intLit {(all ++ [b - 7, b + 5]).map intLit}"
  IO.println s!"repr {all.map toString}"
  IO.println s!"toNat {all.map Int.toNat} natAbs {all.map Int.natAbs}"
  IO.println s!"absSum {absSum (-1000 + b) 2001 0} {absSum (-p61 - 3) 7 0}"
