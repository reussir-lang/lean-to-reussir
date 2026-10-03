/-! Runtime test: `Int` boundary sweep. Every pair of 27 values (±2^31,
±2^62, Int64 min/max ±1, ±2^64, ±2^100, ±10^30) through `+ - * / %`, `tdiv`,
`tmod`, `fdiv`, `fmod` and comparisons; per value `neg`, `natAbs`, `toNat`,
`sign`, `~~~`, `>>>`/`<<<` by 1..200, `bmod`/`bdiv` by 7 and 0, `^3`,
`toNat?`, `gcd`/`lcm`; `negSucc`/`ofNat` at 2^63, 2^64, 2^70 seen by a match;
Int64-min / -1 in every division flavour; multiplication overflow edges.
From the round-6 adversarial reviewers, area numbers (adv6/numbers), check
IArith. -/

-- Int arithmetic, all division flavours, conversions; runtime operands.
@[noinline] def bi (n : Int) : Int := n
@[noinline] def bn (n : Nat) : Nat := n

def i64max : Int := 9223372036854775807
def i64min : Int := -9223372036854775808

def vals : List Int :=
  [0, 1, -1, 2, -2, 7, -7, 2^31 - 1, -2^31, 2^31, -2^31 - 1, 2^32, -2^32, 2^62, -2^62,
   i64max, i64min, i64max + 1, i64min - 1, 2^64, -2^64, 2^64 - 1, -(2^64) + 1, 2^100 + 3, -(2^100) - 3, 10^30, -(10^30)]

def main (args : List String) : IO Unit := do
  let z : Int := args.length
  let vs := vals.map (· + z)
  let mut i := 0
  for a in vs do
    let mut j := 0
    for b in vs do
      let a' := bi a
      let b' := bi b
      IO.println s!"{i},{j}: + {a' + b'} - {a' - b'} * {a' * b'} / {a' / b'} % {a' % b'} t/ {a'.tdiv b'} t% {a'.tmod b'} f/ {a'.fdiv b'} f% {a'.fmod b'} < {decide (a' < b')} <= {decide (a' ≤ b')} == {a' == b'}"
      j := j + 1
    let a' := bi a
    IO.println s!"{i}: neg {-a'} abs {a'.natAbs} toNat {a'.toNat} sign {a'.sign} not {~~~a'} >>1 {a' >>> bn 1} >>63 {a' >>> bn 63} >>64 {a' >>> bn 64} >>200 {a' >>> bn 200} <<3 {a' <<< bn 3} <<64 {a' <<< bn 64} bmod7 {a'.bmod (bn 7)} bdiv7 {a'.bdiv (bn 7)} bmod0 {a'.bmod (bn 0)} bdiv0 {a'.bdiv (bn 0)} pow3 {a' ^ (bn 3)} toNat? {a'.toNat?} repr {repr a'} gcd {Int.gcd a' (bi 6)} lcm {Int.lcm a' (bi (-4))}"
    i := i + 1
  -- negSucc
  for n in [0, 1, 2^31 - 1, 2^31, 2^63 - 2, 2^63 - 1, 2^63, 2^64 - 1, 2^64, 2^70] do
    let k := Int.negSucc (bn n)
    IO.println s!"negSucc {n} = {k} natAbs {k.natAbs} -k {-k} k+1 {k + 1} match {match k with | .ofNat m => s!"ofNat {m}" | .negSucc m => s!"negSucc {m}"}"
  -- ofNat at boundaries, then match
  for n in [0, 2^63 - 1, 2^63, 2^64 - 1, 2^64, 2^65] do
    let k : Int := Int.ofNat (bn n)
    IO.println s!"ofNat {n} = {k} {match k with | .ofNat m => s!"ofNat {m}" | .negSucc m => s!"negSucc {m}"} {-k}"
  -- division by zero all flavours on big
  let big := bi (2^100)
  IO.println s!"div0: {big / 0} {big % 0} {big.tdiv 0} {big.tmod 0} {big.fdiv 0} {big.fmod 0} {(-big) / 0} {(-big) % 0}"
  IO.println s!"min ops: {i64min / bi (-1)} {i64min % bi (-1)} {i64min.tdiv (bi (-1))} {i64min.tmod (bi (-1))} {i64min.fdiv (bi (-1))} {i64min.fmod (bi (-1))} {i64min * bi (-1)} {-(bi i64min)} {i64min.natAbs} {i64min - bi 1} {i64max + bi 1}"
  IO.println s!"mul edges: {bi i64max * bi 2} {bi i64max * bi (-1)} {bi (2^32) * bi (2^31)} {bi (-(2^32)) * bi (2^31)} {bi (2^32) * bi (-(2^31))} {bi (3037000499) * bi 3037000499} {bi (3037000500) * bi 3037000500} {bi i64max * bi i64max}"
  IO.println s!"half edges: {bi 2147483647 * bi 2147483647} {bi (-2147483647) * bi (-2147483648)} {bi (-2147483648) * bi (-2147483648)} {bi 4294967295 * bi 4294967295}"
  IO.println s!"norm: {(bi (2^64) - bi (2^64 - 5))} {(bi (2^64) - bi (2^64 - 5)) == 5} {(bi (-(2^64)) + bi (2^64)) == 0} {bi (2^64) / bi (2^64)} {(bi (2^64) / bi (2^64)) == 1}"
  IO.println s!"cmp: {repr (compare (bi (2^64)) (bi 5))} {repr (compare (bi (-(2^64))) (bi 5))} {repr (compare (bi 5) (bi (-(2^64))))} {repr (compare (bi (-(2^64))) (bi (-(2^65))))} {max (bi (-(2^64))) (bi (-3))} {min (bi (-(2^64))) (bi (-3))}"
  IO.println s!"pow: {(bi (-2)) ^ (bn 63)} {(bi (-2)) ^ (bn 64)} {(bi (-3)) ^ (bn 41)} {(bi 0) ^ (bn 0)} {(bi (-1)) ^ (bn 1001)}"
  IO.println s!"subNatNat: {Int.subNatNat (bn 3) (bn 10)} {Int.subNatNat (bn (2^64)) (bn 1)} {Int.subNatNat (bn 0) (bn (2^64))}"
  IO.println s!"toString: {toString (bi i64min)} {toString (bi (-(2^200)))} {(bi (-5)).repr}"

