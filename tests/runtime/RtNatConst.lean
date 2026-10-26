/-! Runtime test: constants whose value is a big `Nat` or `Int` (natively
outside the one-word small ranges: a `Nat` of 2^63 or more, an `Int`
outside `int32`; a heap integer of Reussir's outside [-2^61, 2^61)), used in
a loop, next to constants with small values. alloc-check.sh
(RtNatConst.alloc) checks that the loop's allocations grow no faster than
native's, none: a big constant is made once however many iterations run
(RV8N-01: the cheap-consts pass recomputed such constants, so one was
allocated at every use). Under Reussir's representation a big literal is
a static object and Reussir folds arithmetic on constants (`NSB` and `NSC`,
`Int.negSucc` of literals, are static too, even when recomputed), so `PB`
and `PI` are computed by a loop: made once in their once-cells, they cost
nothing per iteration, while a constant recomputed at every use allocates
at every use. Size argument: the number of iterations. -/

def K : Int := 3000000000
def KN : Int := -5000000000
def NS : Int := Int.negSucc 3000000000
def B : Nat := 9223372036854775808
def S : Nat := Nat.succ 9223372036854775807
def smallI : Int := -2147483648
def smallNS : Int := Int.negSucc 2147483647
def smallN : Nat := 9223372036854775807
def NSB : Int := Int.negSucc 4611686018427387904
def NSC : Int := Int.negSucc 9223372036854775808
def PB : Nat := (List.range 3).foldl (fun a _ => a * 4294967296 + 7) 1
def PI : Int := -((List.range 3).foldl (fun a _ => a * 4294967296 + 9) (1 : Int))

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
    if NSB < x then acc := acc + 1
    if NSC < x then acc := acc + 1
    if i < PB then acc := acc + 1
    if PI < x then acc := acc + 1
  return acc

def main (args : List String) : IO Unit := do
  let n := (args.head?.bind String.toNat?).getD 1000
  IO.println s!"{loop n} {K} {KN} {NS} {B} {S} {smallI} {smallNS} {smallN} {NSB} {NSC} {PB} {PI}"
