/-! Runtime test: `Int` values at the edges of a box's immediates, through
boxes (a `List`, an `Option`, a pair, a polymorphic function) and back, then
used. Lean boxes an `Int` in the `int32` range as the scalar of its 32 bits
and any other as an object. Under `--int-backend rcgmp` lean2rr also boxes
an `Int` in [2^32, 2^62) or [-2^62, -2^31) as an immediate (natively an
object, whose word no program can depend on), and the others as a cell:
2^31 - 1, 2^31, 2^32 - 1, 2^32, 2^62 - 1, 2^62 and the negative edges sit on
both sides of each rule. The `int32` values are also read through
`unsafeCast` at `UInt32` and back (natively the boxed scalar's word). -/

@[noinline] def viaBox {α : Type} (x : α) : α := x

def edges : List Int :=
  [0, -1, 2147483647, 2147483648, 4294967295, 4294967296,
   4611686018427387903, 4611686018427387904, 9223372036854775807, 9223372036854775808,
   -2147483648, -2147483649, -4294967295, -4294967296,
   -4611686018427387904, -4611686018427387905, -9223372036854775808, -9223372036854775809]

@[noinline] unsafe def asU32s (xs : List Int) : List UInt32 := unsafeCast xs
@[noinline] unsafe def asInts (xs : List UInt32) : List Int := unsafeCast xs

def main (args : List String) : IO Unit := do
  let k : Int := args.length
  for a in edges do
    for c in [a, a + k, a - k] do
      let b := viaBox c
      let o : Option Int := some c
      let os : List (Option Int) := [o, none, some (c + 1)]
      IO.println s!"{c}: {b} {o.getD 0} {(os.head!).getD 0} {(os.getLast!).getD 0} {b == c} {b + 1} {b - 1} {b * 2} {b / 3} {b % 7} {b.toNat} {b.natAbs} {(viaBox (c, c - 1)).2}"
  let boxed : List Int := edges.map (· + k)
  IO.println s!"sum {boxed.foldl (· + ·) 0} max {boxed.foldl max 0} min {boxed.foldl min 0} sorted {boxed.mergeSort (· ≤ ·)}"
  let smalls : List Int := [2147483647, -2147483648, -1, 0, 5]
  IO.println s!"{unsafe asU32s smalls}"
  IO.println s!"{unsafe asInts [0xFFFFFFFF, 0x80000000, 7, 0]}"
