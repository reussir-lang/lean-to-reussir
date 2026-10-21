/-! Runtime test (typed arrays, clean step B1; re-review probe SD2): the
entries of a `map` split only for pointer kinds that end up boxed go back
to the loop in place (`revertPtrSplits`), which finds the split's own
source and result parameters by names no user code has. Here a map's
lambda captures two arrays named `src` and `dst`, which Lean's
specializer puts first among the loop's parameters with their user
names: matched by those names, the revert dropped the wrong argument
(an internal panic where native prints the result). Rounds of
`String → Nat → String` maps beside it keep every kind boxed. Argument:
n. -/

def tbl : Array String := #["a", "bb", "ccc", "dddd"]

@[noinline] def step (src dst : Array String) (a : Array String) : Array Nat :=
  a.map fun s => s.length + src[0]!.length + dst[1]!.length

def main (args : List String) : IO Unit := do
  let n := (args[0]? >>= String.toNat?).getD 1000
  let mut a : Array String := (Array.range n).map fun i => tbl[i % 4]!
  let mut acc := 0
  for r in [0:10] do
    let b : Array Nat := a.map fun s => s.length + r
    acc := acc + b[n / 2]!
    a := b.map fun k => tbl[k % 4]!
  let c := step tbl a a
  IO.println s!"{acc} {a.size} {a[n / 3]!} {c[n / 2]!}"
