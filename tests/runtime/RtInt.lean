/-! Runtime test: `Int` externs (small/big boundaries around ±2^63 and ±2^64,
all division conventions, division by zero, conversions, bitwise ops on
negative numbers). -/

def two63 : Int := 9223372036854775808
def two64 : Int := 18446744073709551616

def samples (k : Int) : List Int :=
  [0, 1, -1, 2, -2, 7, -7, 2147483647, -2147483648, 2147483648, -2147483649,
   4294967296, -4294967296, two63 - 1, -two63, two63, -two63 - 1, two64 - 1, -two64 + 1,
   two64, -two64, two64 + 1, -(two64 * two64) - 12345, 170141183460469231731687303715884105727, k]

def divisors : List Int := [0, 1, -1, 2, -2, 3, -3, 7, -7, two63, -two63, two64, -two64 - 5]

def showDiv (a b : Int) : String :=
  s!"{a} {b}: / {a / b} % {a % b} tdiv {a.tdiv b} tmod {a.tmod b} fdiv {a.fdiv b} fmod {a.fmod b} " ++
  s!"ediv {Int.ediv a b} emod {Int.emod a b}"

def main (args : List String) : IO Unit := do
  let k : Int := -(args.length + 11 : Nat)
  let xs := samples k
  for a in xs do
    for b in xs do
      if b == 0 || b == 1 || b == -1 || b == two63 || b == -two63 - 1 || b == two64 || b == k then
        IO.println s!"{a} {b}: + {a + b} - {a - b} * {a * b} < {decide (a < b)} <= {decide (a ≤ b)} == {decide (a = b)} cmp {repr (compare a b)}"
  for a in xs do
    for b in divisors do
      IO.println (showDiv a b)
  for a in xs do
    IO.println s!"{a}: neg {-a} natAbs {a.natAbs} toNat {a.toNat} sign {a.sign} abs {a.natAbs} nonneg {decide (0 ≤ a)} emod4 {a % 4} ediv4 {a / 4}"
    IO.println s!"  toInt8 {a.toInt8} toInt16 {a.toInt16} toInt32 {a.toInt32} toInt64 {a.toInt64} toISize {a.toISize}"
    IO.println s!"  bmod 5 {Int.bmod a 5} bdiv 5 {Int.bdiv a 5} bmod 2^64 {Int.bmod a 18446744073709551616}"
    IO.println s!"  >>> 1 {a >>> 1} >>> 3 {a >>> 3} >>> 64 {a >>> 64} >>> 100 {a >>> 100}"
    IO.println s!"  pow3 {a ^ 3} repr {repr a} toString {toString a} hash {hash a}"
  for a in [0, 5, -5, 12, -12, two64 + 3, -two64 - 3] do
    for b in [0, 3, -3, 10, -10, two63, -two63] do
      IO.println s!"{a} {b}: not {~~~a} shl {a <<< b.toNat % 70} gcd {Int.gcd a b} lcm {Int.lcm a b}"
  IO.println s!"negSucc {Int.negSucc 0} {Int.negSucc 5} {Int.negSucc 9223372036854775807} {Int.negSucc 9223372036854775808} {Int.negSucc 18446744073709551615}"
  IO.println s!"ofNat {Int.ofNat 9223372036854775807} {Int.ofNat 9223372036854775808} {Int.ofNat 18446744073709551616}"
  IO.println s!"toFloat {(-3 : Int).toNat} {Float.ofInt (-5)} {Float.ofInt (two64 * 3)} {Float.ofInt (-two63)}"
  IO.println s!"sum {(List.range 1000).foldl (fun (acc : Int) (i : Nat) => acc + (i : Int) * (if i % 2 == 0 then 1 else -1) * two63) 0}"
  IO.println s!"min/max {min (-3 : Int) 4} {max (-3 : Int) 4} {min two64 (-two64)}"
