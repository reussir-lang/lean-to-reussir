/-! Runtime test: `Nat` externs (small/big boundaries, truncation, division by
zero, shifts, bitwise, pow, gcd, log2, conversions). -/

def two64 : Nat := 18446744073709551616
def two63 : Nat := 9223372036854775808
def big1 : Nat := 123456789012345678901234567890123456789
def big2 : Nat := 98765432109876543210

/-- Values straddling the machine-word boundaries. Built at runtime so the
compiler cannot fold them. -/
def samples (k : Nat) : List Nat :=
  [0, 1, 2, 3, 7, 10, 255, 256, 65535, 4294967295, 4294967296,
   two63 - 1, two63, two63 + 1, two64 - 2, two64 - 1, two64, two64 + 1,
   2 * two64, big2, big1, k]

def showOps (a b : Nat) : String :=
  s!"{a} {b}: + {a + b} - {a - b} * {a * b} / {a / b} % {a % b} " ++
  s!"== {decide (a = b)} < {decide (a < b)} <= {decide (a ≤ b)} " ++
  s!"&&& {a &&& b} ||| {a ||| b} ^^^ {a ^^^ b} gcd {Nat.gcd a b} " ++
  s!"beq {a == b} ble {Nat.ble a b} lcm {Nat.lcm a b}"

def main (args : List String) : IO Unit := do
  let k := args.length + 5
  let xs := samples k
  for a in xs do
    for b in [0, 1, 3, 4294967296, two64 - 1, two64, big2] do
      IO.println (showOps a b)
  for a in xs do
    IO.println s!"log2 {a} = {Nat.log2 a}; pred {a.pred}; succ {a.succ}; sqrt {Nat.sqrt a}"
  for a in xs do
    IO.println s!"toUInt8 {a.toUInt8} toUInt16 {a.toUInt16} toUInt32 {a.toUInt32} toUInt64 {a.toUInt64} toUSize {a.toUSize}"
    IO.println s!"toInt8 {a.toInt8} toInt16 {a.toInt16} toInt32 {a.toInt32} toInt64 {a.toInt64} toISize {a.toISize}"
    IO.println s!"toFloat {a.toFloat} toInt {(a : Int)} neg {-(a : Int)} isPowerOfTwo {decide (a.isPowerOfTwo)}"
  -- shifts
  for a in [0, 1, 5, two63, two64 - 1, big1] do
    for s in [0, 1, 7, 31, 32, 33, 63, 64, 65, 127, 128, 200] do
      IO.println s!"{a} <<< {s} = {a <<< s}; {a} >>> {s} = {a >>> s}"
  IO.println s!"0 <<< big = {(0 : Nat) <<< two64}"
  IO.println s!"5 >>> big = {(5 : Nat) >>> two64}; big >>> big = {big1 >>> two64}"
  -- pow
  for b in [0, 1, 2, 3, 10, 255, 4294967296, big2] do
    for e in [0, 1, 2, 3, 31, 32, 63, 64, 65, 100] do
      IO.println s!"{b} ^ {e} = {b ^ e}"
  IO.println s!"2^1000 = {2 ^ 1000}"
  IO.println s!"3^500 % 1000007 = {3 ^ 500 % 1000007}"
  -- factorial and fibonacci (bignum growth)
  let fact := (List.range 60).foldl (fun acc i => acc * (i + 1)) 1
  IO.println s!"60! = {fact}"
  IO.println s!"60! / 2^56 = {fact / 2 ^ 56} rem {fact % 2 ^ 56}"
  IO.println s!"60! / big1 = {fact / big1} rem {fact % big1}"
  let rec fib : Nat → Nat → Nat → Nat
    | 0, a, _ => a
    | n + 1, a, b => fib n b (a + b)
  IO.println s!"fib 300 = {fib 300 0 1}"
  IO.println s!"fib 300 - fib 299 = {fib 300 0 1 - fib 299 0 1}"
  IO.println s!"sub trunc {(3 : Nat) - 5} {big2 - big1} {two64 - two64}"
  IO.println s!"div exact {Nat.divExact (big1 * 7) 7 (Nat.dvd_mul_left 7 big1)}"
  -- digits / repr
  IO.println s!"toDigits 16 {Nat.toDigits 16 big1} repr {Nat.repr two64} {repr big2}"
  IO.println s!"toSuperscript {Nat.toSuperscriptString 1234567890}"
  IO.println s!"min {min big1 big2} max {max big1 big2} compare {repr (compare big1 big2)} {repr (compare 3 3)} {repr (compare two64 5)}"
  IO.println s!"hash {hash (5 : Nat)} {hash two64} {hash big1}"
