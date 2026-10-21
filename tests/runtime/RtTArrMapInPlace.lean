/-! Runtime test (typed arrays, clean step B1; review probe D): rounds of
`Array.map` between two pointer kinds (`String → Nat → String`) on a
unique array, natively in place. Stage 3 splits the first `map` of a round
(a new `Array Nat` per map) before the whole-program check decides the
kinds; here the second `map` keeps Lean's loop over `Array NonScalar`, so
`Nat` and `LStr` end up boxed, and the split is entered in place again
(`revertPtrSplits`). `RtTArrMapInPlace.alloc` checks that the bytes grow
no faster than native's from n = 10000 to n = 40000 (with the split, 96
bytes per element against native's 8). Argument: n. -/

def tbl : Array String := #["a", "bb", "ccc", "dddd"]

def main (args : List String) : IO Unit := do
  let n := (args[0]? >>= String.toNat?).getD 1000
  let mut a : Array String := (Array.range n).map fun i => tbl[i % 4]!
  let mut acc := 0
  for r in [0:10] do
    let b : Array Nat := a.map fun s => s.length + r
    acc := acc + b[n / 2]!
    a := b.map fun k => tbl[k % 4]!
  IO.println s!"{acc} {a.size} {a[n / 3]!}"
