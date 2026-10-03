/-! Runtime test: `Nat` boundary sweep. Every pair of 21 values around the
small/big boundaries (2^31, 2^32, 2^62, 2^63, 2^64, 2^65, 2^127, 2^128, 10^40)
through `+ - * / %`, comparisons and `compare`; then 12 values up to 3^90
through `&&& ||| ^^^ gcd lcm`, `log2`/`sqrt`/`testBit`, shifts by 0..200 and
by 2^64, a pow table (u64 overflow edges, 0^0, 1^10^6), results that become
small again after `sub`/`div`/`mod`/`xor`. Operands pass through a
`@[noinline]` identity so nothing is folded at compile time.
From the round-6 adversarial reviewers, area numbers (adv6/numbers),
checks NArith and NBits. -/

namespace NArith
-- from adv6/numbers/NArith.lean
-- Nat arithmetic at boundaries, with runtime (non-folded) operands.
@[noinline] def bb (n : Nat) : Nat := n

def vals : List Nat :=
  [0, 1, 2, 2^31 - 1, 2^31, 2^32 - 1, 2^32, 2^32 + 1, 2^62, 2^63 - 1, 2^63, 2^63 + 1,
   2^64 - 1, 2^64, 2^64 + 1, 2^65, 2^127, 2^128 - 1, 2^128, 2^128 + 1, 10^40]

def main (args : List String) : IO Unit := do
  let z := args.length
  let vs := vals.map (· + z)
  let mut i := 0
  for a in vs do
    let mut j := 0
    for b in vs do
      let a' := bb a
      let b' := bb b
      IO.println s!"{i},{j}: + {a' + b'} - {a' - b'} * {a' * b'} / {a' / b'} % {a' % b'} < {decide (a' < b')} <= {decide (a' ≤ b')} == {a' == b'} cmp {repr (compare a' b')}"
      j := j + 1
    i := i + 1
  -- huge
  let h := bb (10^1000 + z)
  let h2 := bb (h * h + 7)
  IO.println s!"h2 % 1000003 = {h2 % 1000003}"
  IO.println s!"h2 / h = {h2 / h == h}"
  IO.println s!"h2 - h*h = {h2 - h * h}"
  IO.println s!"h - h2 = {h - h2}"
  IO.println s!"(h2 % h) = {h2 % h}"
  IO.println s!"h2 / 0 = {h2 / bb 0}  h2 % 0 == h2 {h2 % bb 0 == h2}"
  IO.println s!"0 / h = {bb 0 / h}  5 % h = {bb 5 % h}"
  IO.println s!"len {(toString h2).length}"
  IO.println s!"succ/pred: {Nat.succ (bb (2^64-1))} {Nat.pred (bb (2^64))} {Nat.pred (bb 0)} {Nat.pred (bb (2^128))}"
  -- sub to exactly small boundary
  IO.println s!"sub-norm: {bb (2^64) - bb 1} {bb (2^64 + 5) - bb (2^64)} {(bb (2^64 + 5) - bb (2^64)) == 5} {bb (2^128) - bb (2^128 - 2^64)}"
  IO.println s!"div-norm: {bb (2^64) / bb 2} {bb (2^128) / bb (2^64)} {(bb (2^128) / bb (2^64)) == 2^64} {(bb (2^127) / bb (2^64)) == 2^63}"
  IO.println s!"mod-norm: {bb (2^64 + 3) % bb (2^64)} {(bb (2^64 + 3) % bb (2^64)) + 1} {bb (2^128 + 2^64 - 1) % bb (2^64)}"
  IO.println s!"mul-zero: {bb (2^100) * bb 0} {bb 0 * bb (2^100)} {(bb (2^100) * bb 0) == 0}"
  IO.println s!"mul-wide: {bb (2^32) * bb (2^32)} {bb (2^63) * bb 2} {bb (2^64 - 1) * bb (2^64 - 1)} {bb (2^32 + 1) * bb (2^32 - 1)}"
  IO.println s!"add-wide: {bb (2^64 - 1) + bb 1} {bb (2^63) + bb (2^63)} {bb (2^64 - 1) + bb (2^64 - 1)}"
end NArith

namespace NBits
-- from adv6/numbers/NBits.lean
-- Nat bitwise ops, shifts, log2, sqrt, pow, gcd/lcm on big values.
@[noinline] def bb (n : Nat) : Nat := n

def vals : List Nat :=
  [0, 1, 3, 2^32 - 1, 2^63 - 1, 2^63, 2^64 - 1, 2^64, 2^64 + 1, 2^100 + 12345, 2^128 - 1, 3^90]

def main (args : List String) : IO Unit := do
  let z := args.length
  let vs := vals.map (· + z)
  let mut i := 0
  for a in vs do
    let mut j := 0
    for b in vs do
      let a' := bb a
      let b' := bb b
      IO.println s!"{i},{j}: & {a' &&& b'} | {a' ||| b'} ^ {a' ^^^ b'} gcd {Nat.gcd a' b'} lcm {Nat.lcm a' b'}"
      j := j + 1
    IO.println s!"{i}: log2 {Nat.log2 (bb a)} sqrt {Nat.sqrt (bb a)} testBit0 {(bb a).testBit 0} tb63 {(bb a).testBit 63} tb64 {(bb a).testBit 64} tb200 {(bb a).testBit 200}"
    for s in [0, 1, 31, 32, 63, 64, 65, 127, 128, 200] do
      IO.println s!"  {i} s{s}: << {(bb a) <<< (bb s)} >> {(bb a) >>> (bb s)}"
    i := i + 1
  -- shifts by big amounts (right): fine
  IO.println s!"shr big: {bb 5 >>> bb (2^64)} {bb (2^100) >>> bb (2^64)} {bb (2^100) >>> bb (2^40)} {bb 0 <<< bb (2^70)}"
  -- pow
  for (b, e) in [(0, 0), (0, 5), (1, 1000000), (2, 63), (2, 64), (2, 65), (3, 40), (3, 41), (10, 19), (10, 20), (2^32, 2), (2^32 - 1, 2), (7, 0), (2^64, 0), (2^64, 1), (2^64, 3), (255, 8)] do
    IO.println s!"pow {b} {e} = {(bb b) ^ (bb e)}"
  -- pow overflow detection near u64 boundary
  IO.println s!"pow edge: {(bb 4294967296) ^ (bb 2)} {(bb 65536)^(bb 4)} {(bb 2642245)^(bb 3)} {(bb 2642246)^(bb 3)}"
  IO.println s!"log2 big: {Nat.log2 (bb (10^1000))} {Nat.log2 (bb (2^4000))}"
  IO.println s!"sqrt big: {Nat.sqrt (bb (10^100))} {Nat.sqrt (bb (2^128 - 1))} {Nat.sqrt (bb (2^64))}"
  IO.println s!"gcd zero: {Nat.gcd (bb 0) (bb 0)} {Nat.gcd (bb 0) (bb (2^70))} {Nat.gcd (bb (2^70)) (bb 0)} {Nat.lcm (bb 0) (bb (2^70))}"
  IO.println s!"gcd mixed: {Nat.gcd (bb (2^70 * 3)) (bb 6)} {Nat.gcd (bb 6) (bb (2^70*3))} {Nat.gcd (bb (2^64 + 1)) (bb 274177)}"
  IO.println s!"xor-norm: {(bb (2^64 + 5)) ^^^ (bb (2^64))} {((bb (2^64 + 5)) ^^^ (bb (2^64))) == 5} {(bb (2^70)) &&& (bb (2^70 - 1))} {((bb (2^70)) &&& (bb (2^70 - 1))) == 0}"
  IO.println s!"testBit big: {(bb (2^1000)).testBit 1000} {(bb (2^1000)).testBit 999} {(bb (2^1000)).testBit (bb (2^64))}"
end NBits

def main : IO Unit := do
  IO.println "=== NArith"
  NArith.main []
  IO.println "=== NBits"
  NBits.main []
