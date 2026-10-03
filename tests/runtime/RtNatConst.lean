/-! Runtime test: constants whose value is a big `Nat` or `Int` (outside
the one-word small ranges: a `Nat` of 2^63 or more, an `Int` outside
`int32`), used in a loop, next to constants with small values.
`nat-alloc-check.sh` builds it with leanrt's big-number counters and
checks that the big numbers are made once however many iterations run
(RV8N-01: the cheap-consts pass recomputed such constants, so one was
allocated at every use). Size argument: the number of iterations. -/

def K : Int := 3000000000
def KN : Int := -5000000000
def NS : Int := Int.negSucc 3000000000
def B : Nat := 9223372036854775808
def S : Nat := Nat.succ 9223372036854775807
def smallI : Int := -2147483648
def smallNS : Int := Int.negSucc 2147483647
def smallN : Nat := 9223372036854775807

@[noinline] def loop (n : Nat) : Int := Id.run do
  let mut acc : Int := 0
  for i in [0:n] do
    let x : Int := i
    if x < K then acc := acc + 1
    if KN < x then acc := acc + 1
    if NS < x then acc := acc + 1
    if i < B then acc := acc + 1
    if i < S then acc := acc + 1
    if smallI < x then acc := acc + 1
    if smallNS < x then acc := acc + 1
    if i < smallN then acc := acc + 1
  return acc

def main (args : List String) : IO Unit := do
  let n := (args.head?.bind String.toNat?).getD 1000
  IO.println s!"{loop n} {K} {KN} {NS} {B} {S} {smallI} {smallNS} {smallN}"
