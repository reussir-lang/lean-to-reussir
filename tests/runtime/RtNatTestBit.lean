/-! Runtime test: `Nat.testBit` on small and big values, at indices below,
at and past the value's bit length, up to an index of 2^64 and more (no
number has such a bit). lean2rr may compute it in place (`l2r_nat_test_bit`:
under `--int-backend rcgmp` rcgmp's `testbiti`, where Lean's definition
builds `m >>> i`); the answers are Lean's. `Nat.testBit` also runs as a
function value (`m.testBit` and `Nat.testBit` passed to functions that are
not inlined), which calls its instance's own code (under rcgmp one call of
`l2r_nat_test_bit`). -/

def vals (k : Nat) : List Nat :=
  [0, 1, 5 + k, 2 ^ 31, 2 ^ 61 - 1, 2 ^ 61, 2 ^ 63 + 5, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 100 + 2 ^ 37 + k, 3 ^ 90]

def idxs : List Nat :=
  [0, 1, 2, 31, 37, 60, 61, 62, 63, 64, 65, 99, 100, 101, 142, 1000, 2 ^ 32, 2 ^ 63, 2 ^ 64, 2 ^ 70]

/-- Each index's bit, by `f` (not inlined: `f` stays a function value). -/
@[noinline] def bitsOf (f : Nat → Bool) (is : List Nat) : List Bool := is.map f

/-- The same through a function of two arguments, applied to `m` here. -/
@[noinline] def bitsOf2 (f : Nat → Nat → Bool) (m : Nat) (is : List Nat) : List Bool := is.map (f m)

def showBits (bs : List Bool) : String := String.mk (bs.map fun b => if b then '1' else '0')

def main (args : List String) : IO Unit := do
  let k := args.length
  for m in vals k do
    let bits := idxs.map (fun i => if m.testBit i then '1' else '0')
    IO.println s!"{m}: {String.mk bits} {showBits (bitsOf m.testBit idxs)} {showBits (bitsOf2 Nat.testBit m idxs)}"
  -- A bit matrix as the regex benchmark keeps one: set bits, then read them.
  let mut x : Nat := 0
  for i in [0:300] do
    if i % 7 == 3 || i % 11 == 5 then x := x ||| (1 <<< i)
  let mut ones := 0
  for i in [0:310] do
    if x.testBit i then ones := ones + 1
  IO.println s!"matrix ones {ones} log2 {Nat.log2 x}"
