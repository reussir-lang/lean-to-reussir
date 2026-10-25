/-! Runtime test: `Float.ofNat`/`Nat.toFloat` and `Float.ofInt`/`Int.toFloat`
on values computed at run time (not folded by `float-lits`): small values,
the edges of the immediates (2^31, 2^32, 2^61, 2^62, 2^63, 2^64), the last
exact integers around 2^53, ties to even at several magnitudes (one decided
by a bit far below the halfway point), the largest finite double and the
overflow edge to an infinity (`(2^54 - 1) * 2^970`, halfway between the
largest finite double and 2^1024, goes up), far past it, and the negatives
of all of them. Each conversion runs as a direct call and through a function
value. lean2rr computes them under `--int-backend rcgmp` with `sitofp`
(`prelude-int-ops`: `l2r_float_of_nat`, `l2r_float_of_int`), natively
Lean's `Float.ofScientific`; the bits must agree. -/

def maxFinite : Nat := (2 ^ 53 - 1) * 2 ^ 971
def overflowEdge : Nat := (2 ^ 54 - 1) * 2 ^ 970

def nats : List Nat :=
  [0, 1, 2, 7, 2 ^ 31 - 1, 2 ^ 31, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 32 + 1,
   2 ^ 53 - 1, 2 ^ 53, 2 ^ 53 + 1, 2 ^ 53 + 2, 2 ^ 53 + 3, 2 ^ 54 + 2, 2 ^ 54 + 6,
   2 ^ 61 - 1, 2 ^ 61, 2 ^ 61 + 1, 2 ^ 62 - 1, 2 ^ 62, 2 ^ 63 - 1, 2 ^ 63, 2 ^ 63 + 1,
   2 ^ 64 - 1, 2 ^ 64, 2 ^ 64 + 2 ^ 11, 2 ^ 64 + 2 ^ 11 + 1, 2 ^ 64 + 3 * 2 ^ 11,
   2 ^ 100 + 2 ^ 47, 2 ^ 100 + 2 ^ 47 + 1, 2 ^ 100 + 3 * 2 ^ 47,
   2 ^ 200 + 2 ^ 147, 2 ^ 200 + 2 ^ 147 + 1, 2 ^ 200 + 2 ^ 147 - 1,
   3 ^ 200, 10 ^ 22, 10 ^ 23, 10 ^ 308,
   maxFinite - 1, maxFinite, maxFinite + 1, overflowEdge - 1, overflowEdge, overflowEdge + 1,
   2 ^ 1024 - 1, 2 ^ 1024, 10 ^ 309, 2 ^ 2000]

/-- Applies `f` to each element (not inlined: `f` is a function value). -/
@[noinline] def mapF {α : Type} (f : α → Float) (xs : List α) : List Float := xs.map f

def fmt (x : Float) : String := s!"{x.toBits} {x}"

def main (args : List String) : IO Unit := do
  let k := args.length
  let ns : List Nat := nats.map (· + k)
  let edges : List Int := [-(2 ^ 31 : Int) - 1, -(2 ^ 62 : Int) - 1, -(2 ^ 63 : Int) - 1]
  let is : List Int := ns.map (fun n => Int.ofNat n) ++ ns.map (fun n => -Int.ofNat n)
    ++ edges.map (· - Int.ofNat k)
  for n in ns do
    IO.println s!"ofNat {n.log2}: {fmt (Float.ofNat n)} {(Nat.toFloat n).toBits}"
  for i in is do
    IO.println s!"ofInt {i.natAbs.log2} {decide (i < 0)}: {fmt (Float.ofInt i)} {(Int.toFloat i).toBits}"
  let viaNat := mapF Float.ofNat ns
  let viaNat2 := mapF Nat.toFloat ns
  let viaInt := mapF Float.ofInt is
  let viaInt2 := mapF Int.toFloat is
  IO.println s!"values: {(viaNat.map (·.toBits)) == ns.map (fun n => (Float.ofNat n).toBits)} \
    {(viaNat2.map (·.toBits)) == viaNat.map (·.toBits)} \
    {(viaInt.map (·.toBits)) == is.map (fun i => (Float.ofInt i).toBits)} \
    {(viaInt2.map (·.toBits)) == viaInt.map (·.toBits)}"
  IO.println s!"inf {viaNat.filter (·.isInf) |>.length} {viaInt.filter (·.isInf) |>.length}"
  IO.println s!"bits {viaNat.map (·.toBits)}"
  IO.println s!"bits {viaInt.map (·.toBits)}"
