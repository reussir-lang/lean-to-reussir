-- A map whose function is used at two sites (round 6, RV6L-02): Lean runs
-- the first iteration in a specialization of its own (`spec_2`), which passes
-- the array, with one value written, to the actual loop (`spec_2.spec_2`).
-- Both are split when the element type changes: the loop does not run on an
-- array of `Box`es.
@[noinline] def toFloats (rows : Array (Array Nat)) : Array (Array Float) :=
  rows.map fun r => r.map (·.toFloat)

@[noinline] def rowsOf (n w : Nat) : Array (Array Nat) :=
  (Array.range n).map fun i => (Array.range w).map fun j => i * 10 + j

def main : IO Unit := do
  -- 1: the same nested map at two sites
  let small := (Array.range 3).map fun i => #[i, i + 1]
  IO.println s!"1 {small.map fun r => r.map (·.toFloat)}"
  let big := (Array.range 200000).map fun i => #[i]
  let bf := big.map fun r => r.map (·.toFloat)
  IO.println s!"1 {bf.size} {bf[199999]!} {bf[0]!}"
  -- 2: an empty and a one-row outer array (the loop exits at once / after
  -- the first iteration)
  let e : Array (Array Nat) := #[]
  IO.println s!"2 {e.map fun r => r.map (·.toFloat)} {#[#[7, 8]].map fun (r : Array Nat) => r.map (·.toFloat)}"
  -- 3: shared rows; the source stays unchanged
  let shared := #[1, 2, 3]
  let s3 : Array (Array Nat) := #[shared, shared, shared]
  IO.println s!"3 {s3.map fun r => r.map (·.toFloat)} {s3} {shared}"
  -- 4: Nat to String rows at two sites
  let strs := (rowsOf 3 2).map fun r => r.map toString
  let strs2 := (rowsOf 2 3).map fun r => r.map toString
  IO.println s!"4 {strs} {strs2}"
  -- 5: a flat map with one function at two sites
  let g := fun (x : Nat) => x % 3 == 0
  IO.println s!"5 {(Array.range 7).map g} {(Array.range 4).map g}"
  -- 6: Option results (mapM) at two sites, one failing
  let h := fun (r : Array Nat) => r.mapM fun x => if x < 50 then some x.toFloat else none
  IO.println s!"6 {(rowsOf 3 2).mapM h} {(rowsOf 6 2).mapM h}"
  -- 7: mapIdx at two sites
  let k := fun (i : Nat) (r : Array Nat) => r.map fun x => (x + i).toFloat
  IO.println s!"7 {(rowsOf 3 2).mapIdx k} {(rowsOf 2 2).mapIdx k}"
  -- 8: through a non-inlined function, twice
  IO.println s!"8 {toFloats (rowsOf 2 3)} {(toFloats (rowsOf 4000 25)).foldl (fun a r => a + r.foldl (· + ·) 0) 0}"
