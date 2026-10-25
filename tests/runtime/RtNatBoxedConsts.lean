/-! Runtime test: `Nat` and `Int` constants stored in lists (boxed), at the
edges of the box's immediates: a `Nat` below 2^63 and an `Int` in the
`int32` range, in [2^32, 2^62) or in [-2^62, -2^31) are immediates; a `Nat`
from 2^63, an `Int` in [2^31, 2^32) and one of 2^62 or more in magnitude
are cells. Under `--int-backend rcgmp` a box of a value outside the
immediates is a new leanrt cell, so `boxed-consts` boxes such a constant
once, in a once-cell; one whose box is an immediate is boxed in line
(review of step D: `k5 : Nat := 5` had a once-cell). Checked by
tests/runtime/int-backend-check.sh (the once-cells of the translation);
here the values must be native's. -/

@[noinline] def k5 : Nat := 5
@[noinline] def kN63 : Nat := 2 ^ 63 - 1
@[noinline] def kN64 : Nat := 2 ^ 63
@[noinline] def kI : Int := -7
@[noinline] def kP : Int := 7
@[noinline] def kI31 : Int := 2 ^ 31 - 1
@[noinline] def kI31n : Int := -(2 ^ 31)
@[noinline] def kI31p : Int := 2 ^ 31
@[noinline] def kU32 : Int := 2 ^ 32 - 1
@[noinline] def kI31m : Int := -(2 ^ 31) - 1
@[noinline] def kM : Int := 3000000000
@[noinline] def kW : Int := 2 ^ 32
@[noinline] def kWn : Int := -3000000000
@[noinline] def kW62 : Int := 2 ^ 62 - 1
@[noinline] def kW62n : Int := -(2 ^ 62)
@[noinline] def kB : Int := 2 ^ 62
@[noinline] def kBn : Int := -(2 ^ 62) - 1
@[noinline] def kD : Int := k5 - 9

@[noinline] def pushN (xs : List Nat) : List Nat := k5 :: kN63 :: kN64 :: xs
@[noinline] def pushI (xs : List Int) : List Int :=
  kI :: kP :: kI31 :: kI31n :: kI31p :: kU32 :: kI31m :: kM :: kW :: kWn :: kW62 :: kW62n :: kB :: kBn :: kD :: xs

def main (args : List String) : IO Unit := do
  let k := args.length
  let ns := (List.range 3).foldl (fun acc _ => pushN acc) [k]
  let is := (List.range 3).foldl (fun acc _ => pushI acc) [Int.ofNat k]
  IO.println s!"{ns}"
  IO.println s!"{is}"
  IO.println s!"{ns.foldl (· + ·) 0} {is.foldl (· + ·) 0}"
