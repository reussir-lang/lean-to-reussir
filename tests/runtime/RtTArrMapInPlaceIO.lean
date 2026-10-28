/-! Runtime test (typed arrays; bug hunt of the map loops, 2026-10-27,
HsMaps3; Performance): `RtTArrMapInPlace` with `mapM` in `IO`: rounds of
`String → Nat → String` maps on a unique array, natively in place. Stage 3
splits each `mapM`'s loop (a new `Array Nat`, then a new `Array String`,
per map) before the whole-program check decides the kinds; the
existential `Pk` meets both arrays, so `Nat` and `LStr` end up boxed and
the splits are entered in place again (`revertPtrSplits`). Lean's loop in
`IO` returns an IO result, so `flatten-structs` gives the split instance
and the loop each a worker that returns the result's fields (a tuple), and
the callers call the split's worker (`…_l2r_split.k._l2r_flat`): those
entries call the loop's worker instead (`flattenSplitsAlike`). Before, the
revert knew only the split's own name and left every `mapM` here pushing
onto a new array of boxes. `.l2r-debug`: the number of entries reverted
(on dev 0a1e4391, only the pure `map` that builds the first array);
`.alloc`: bytes grow as natively. Argument: n. -/

def tbl : Array String := #["a", "bb", "ccc", "dddd"]

@[noinline] def lens (a : Array String) (r : Nat) : IO (Array Nat) :=
  a.mapM fun s => do
    if s == "zz" then IO.println "zz"
    pure (s.length + r)

@[noinline] def strs (b : Array Nat) : IO (Array String) :=
  b.mapM fun k => do
    if k == 1000000 then IO.println "big"
    pure tbl[k % 4]!

structure Pk where
  τ : Type
  v : Array τ

@[noinline] def pkSize (p : Pk) : Nat := p.v.size

def main (args : List String) : IO Unit := do
  let n := (args[0]? >>= String.toNat?).getD 1000
  let mut a : Array String := (Array.range n).map fun i => tbl[i % 4]!
  let mut acc := 0
  for r in [0:10] do
    let b ← lens a r
    acc := acc + b[n / 2]!
    a ← strs b
  IO.println s!"{acc} {a.size} {a[n / 3]!} {pkSize ⟨String, a⟩} {pkSize ⟨Nat, (← lens a 0)⟩}"
