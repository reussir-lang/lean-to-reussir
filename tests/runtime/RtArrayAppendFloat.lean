/-! Runtime test: `a ++ b` on `Array Float` (reviewer's repro E19Append).
`Array.append`'s loop reads each element of `b` and pushes it onto `a`:
natively the boxes are shared, and lean2rr passes each element's box on
(`boxedOnlyVars`); it unboxed each `Float` and boxed it again, a new cell
per appended element. The output is checked here; the allocations by
tests/runtime/alloc-check.sh (RtArrayAppendFloat.alloc). Argument: the
length of each array (default 1000). -/
@[noinline] def mkArr (n : Nat) : Array Float := (Array.range n).map (·.toFloat * 0.5)
@[noinline] def app (a b : Array Float) : Array Float := a ++ b
def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 1000
  let a := mkArr n
  let b := mkArr n
  let c := app a b
  IO.println s!"{c.size} {c.foldl (· + ·) 0.0} {a.size} {b.size}"
