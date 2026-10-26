/-! Runtime test: every division of `Nat` and `Int` by 0, 1 and -1 (and by
a big divisor), on immediate and heap operands of Reussir's built-in
integers (rcgmp's immediates are [-2^61, 2^61)): Lean defines
`x / 0 = 0` and `x % 0 = x` for every flavor (`Nat.div`, `Nat.mod`,
`Nat.divExact`, `Int.div`/`Int.mod` (T-rounding), `Int.ediv`/`Int.emod`,
`Int.fdiv`/`Int.fmod`, `Int.bdiv`/`Int.bmod`), where Reussir's own `/`
and `%` end the program. Divisors are computed at run time and also
written as literals. -/

def p (e k : Nat) : Nat := 2 ^ (e + k % 1)

def nats (k : Nat) : List Nat :=
  [0, 1, 7, p 61 k - 1, p 61 k, p 63 k, p 64 k + 3, p 64 k * p 64 k]

def ints (k : Nat) : List Int :=
  (nats k).map (fun (n : Nat) => (n : Int)) ++ (nats k).map (fun (n : Nat) => -(n : Int) - 1)

def natDivs (a b : Nat) : String :=
  s!"{a} {b}: / {a / b} % {a % b} divExact {if b = 0 ∨ a % b = 0 then toString (Nat.div a b) else "-"} " ++
  s!"shiftDiv {a / (b + 1)}"

def intDivs (a b : Int) : String :=
  s!"{a} {b}: / {a / b} % {a % b} div {a.tdiv b} mod {a.tmod b} ediv {a.ediv b} emod {a.emod b} " ++
  s!"fdiv {a.fdiv b} fmod {a.fmod b} bdiv {a.bdiv b.natAbs} bmod {a.bmod b.natAbs}"

def main (args : List String) : IO Unit := do
  let k := args.length
  let z0 := 0 + k
  let one := 1 + k
  let big := p 64 k + 5
  for a in nats k do
    for b in [z0, one, big] do
      IO.println (natDivs a b)
    IO.println s!"{a} lit: / 0 {a / 0} % 0 {a % 0} / 1 {a / 1} % 1 {a % 1}"
    -- `Nat.divExact` with a divisor that divides (and 0).
    IO.println s!"{a} exact: {Nat.divExact (a * 3) 3 (Nat.dvd_mul_left 3 a)} {Nat.divExact a 1 (Nat.one_dvd a)} {Nat.divExact 0 z0 (Nat.dvd_zero z0)}"
  let mone : Int := -(one : Int)
  for a in ints k do
    for b in [(z0 : Int), (one : Int), mone, (big : Int), -(big : Int)] do
      IO.println (intDivs a b)
    IO.println s!"{a} lit: / 0 {a / 0} % 0 {a % 0} tdiv 0 {a.tdiv 0} tmod 0 {a.tmod 0} fdiv 0 {a.fdiv 0} fmod 0 {a.fmod 0} / -1 {a / -1} % -1 {a % -1}"
    IO.println s!"{a} exact: {Int.divExact (3 * a) 3 (Int.dvd_mul_right 3 a)} {Int.divExact (-1 * a) (-1) (Int.dvd_mul_right (-1) a)} {Int.divExact 0 (z0 : Int) (Int.dvd_zero (z0 : Int))}"
