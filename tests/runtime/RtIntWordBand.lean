/-! Runtime test: `Int` arithmetic on values outside the 32-bit small range
and inside the 64-bit one (one-limb big numbers in lean2rr, whose slow
paths compute them as words): results that move into and out of the small
range and past 64 bits, operands still used after the operation (shared
blocks) and temporaries (unique ones), `natAbs`, the comparisons and every
division. The band's values come from the command line's length, so
nothing is folded at compile time. -/

def band (k : Int) : List Int :=
  [0, 1, -1, k, -k, 2147483647, -2147483648, 2147483648, -2147483649, 4294967296 + k, -4294967296 - k,
   3037000499, -3037000499, 3037000500, 9223372036854775807, -9223372036854775808,
   9223372036854775807 - k, -9223372036854775807 + k, 9223372036854775808, 18446744073709551616 + k]

def main (args : List String) : IO Unit := do
  let k : Int := (args.length + 5 : Nat)
  let xs := band k
  let mut acc : Int := 0
  for a in xs do
    for b in xs do
      IO.println s!"{a} {b}: + {a + b} - {a - b} * {a * b} / {a / b} % {a % b} tdiv {a.tdiv b} tmod {a.tmod b} fdiv {a.fdiv b} cmp {repr (compare a b)} == {decide (a = b)} < {decide (a < b)} natAbs {(a - b).natAbs} {(a * b).natAbs}"
      acc := acc + (a + k) * (b - k) - (a * k) / (b + k) + (a - b) % (k - b)
  IO.println s!"acc {acc}"
  -- A walk through the band: products leave 64 bits and divisions bring
  -- them back.
  let mut x : Int := 3
  let mut trace : List Int := []
  for i in [0:300] do
    x := if x.natAbs > 4611686018427387904 then x / 1000003 - i else x * (-7) + i
    if i % 25 == 0 then trace := x :: trace
  IO.println s!"walk {x} {trace}"
