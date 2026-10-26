/-! Runtime test: `Nat` and `Int` values in boxes (the elements of `List`
and `Option`, the fields of a pair), from small values to values far past
the box's immediates (`Nat` 2^63 and up, `Int` from 2^62 in magnitude, and
10^30), built, read back, summed and printed. Under `--int-backend rcgmp`
a big value's box is a leanrt cell that takes the owned rcgmp handle
(`l2r_any_of_big`); tests/runtime/int-backend-check.sh checks that the
translation boxes through it. -/

@[noinline] def nats (k : Nat) : List Nat :=
  [0, 1, k, 2^31, 2^62, 2^63 - 1, 2^63 + k, 2^64 + 5 * k, 10^30 + k]

@[noinline] def ints (k : Nat) : List Int :=
  [0, -1, (k : Int), -(2^31 : Int), 2^62 - 1, 2^62 + k, -(2^62) - k, -(2^63 : Int), 2^64 + k, -(10^25 : Int) - k]

@[noinline] def pick (xs : List Nat) (i : Nat) : Option Nat := xs[i]?

@[noinline] def pair (n : Nat) (i : Int) : Nat × Int := (n * 3, i * 7)

def main : IO Unit := do
  for k in [0, 5, 1000] do
    let ns := nats k
    let is := ints k
    IO.println s!"nats {k}: {ns} sum {ns.foldl (· + ·) 0}"
    IO.println s!"ints {k}: {is} sum {is.foldl (· + ·) 0}"
    IO.println s!"picks: {(List.range 10).map (pick ns)}"
    let ps := (ns.zip is).map fun (n, i) => pair n i
    IO.println s!"pairs: {ps}"
    let doubled := ps.map fun (n, i) => (n + n, i - i * 2)
    IO.println s!"doubled: {doubled}"
