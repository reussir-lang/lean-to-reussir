/-! Runtime test: the shapes of the library's unsafe code in the mono
phase, on typed arrays (design review of the layout redesign, correctness,
DRC-04 and DRC-05): `Array.modify` stores Lean's placeholder
(`unsafeCast ()`, a `PUnit.unit`) in the slot while its function runs, and
`Array.map` runs an in-place loop whose array changes element type (a
`NonScalar` cast). Neither may make the typed arrays change layout. -/
@[noinline] def bumpAt (a : Array Nat) (i : Nat) : Array Nat := a.modify i (· + 1)
@[noinline] def bumpL (a : Array (List Nat)) (i : Nat) : Array (List Nat) := a.modify i (0 :: ·)
@[noinline] def strs (a : Array Nat) : Array String := a.map toString

def main (args : List String) : IO Unit := do
  let n := (args.headD "3").toNat!
  let a := bumpAt (Array.range n) 1
  let b := bumpL #[[1], [2]] 0
  IO.println s!"{a} {b} {strs a}"
