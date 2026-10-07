/-! Runtime test: maps over arrays (written for lean2rr's split-map-loops pass,
which ran such a map as a typed loop writing a second array; since rule 1
the maps run Lean's own loop on the one array type, in place, boxing and
unboxing each element). O7Map: mapM in IO with effects and a throw mid-loop
(caught), StateM, ExceptT, Option, StateT over Except, mapIdxM, mapFinIdxM,
closures reading the source, nested maps, Bool → Option, UInt64 → Nat,
tuples, Float → UInt8, empty arrays. SMapA: 15 nested shapes (Nat →
Bool/Float/UInt8/String/Int, mapIdx capturing the index, 3 levels, chained,
shared rows and outer arrays, empty arrays, a captured outer array, foldl of
maps, List.map inside, values ≥ 2^63 and ≥ 2^64, branching functions,
mapFinIdx, zip).
From the round-7 review, area O (rv7/opts, split-map-loops check O7Map), and
the round-6 review, area lower (rv6/lower, check 5, SMapA). SMapA's shape 6
prints the tuple components with `(·.1)`/`(·.2.1)`/`(·.2.2)`: projection maps
over a parametric structure, which printed empty rows and zeros before the
fix of finding RV7D-01 (e318fbd, a9b89e6). -/

namespace O7Map
-- from rv7/opts/O7Map.lean
def f1 (n : Nat) : IO String := do
  IO.println s!"visit {n}"
  if n == 13 then throw (IO.userError s!"bad {n}")
  pure s!"<{n}>"

def stepS (n : Nat) : StateM Nat Float := do
  modify (· + n)
  return n.toFloat * 1.5 + (← get).toFloat

def stepE (n : Nat) : ExceptT String Id UInt8 :=
  if n > 250 then throw s!"too big {n}" else pure n.toUInt8

def stepO (s : String) : Option Nat := s.toNat?

def stepSE (n : Nat) : StateT (List Nat) (Except String) Bool := do
  modify (n :: ·)
  if n == 99 then throw "ninety-nine"
  return n % 2 == 0

@[noinline] def mkArr (n : Nat) : Array Nat := (Array.range n).map (· * 3)

def main : IO Unit := do
  let a := mkArr 6
  let r ← a.mapM f1
  IO.println r
  try
    let r2 ← (mkArr 10).mapM f1
    IO.println r2
  catch e => IO.println s!"caught {e}"
  let (fs, st) := (mkArr 5).mapM stepS |>.run 7
  IO.println s!"{fs} {st}"
  IO.println (repr ((mkArr 5).mapM stepE |>.run))
  IO.println (repr ((mkArr 100).mapM stepE |>.run))
  IO.println (#["1", "22", "333"].mapM stepO)
  IO.println (#["1", "x", "333"].mapM stepO)
  IO.println (repr (((mkArr 4).mapM stepSE).run []))
  IO.println (repr (((mkArr 40).mapM stepSE).run []))
  let r3 ← (mkArr 4).mapIdxM fun i x => do IO.println s!"idx {i} {x}"; pure (x.toFloat / (i.toFloat + 1))
  IO.println r3
  let r4 ← (mkArr 4).mapFinIdxM fun i x _ => pure s!"{i}:{x}"
  IO.println r4
  let src := mkArr 8
  let m1 := src.map (fun x => x + src.size)
  let m2 := src.mapIdx (fun i x => (src[i]! + x).toUInt64)
  IO.println s!"{m1} {m2} {src}"
  let nested := #[mkArr 2, mkArr 3, #[]].map (·.map (fun x => s!"{x}"))
  IO.println nested
  let bools := (mkArr 7).map (· % 2 == 0)
  let opts := bools.map (fun b => if b then some 1 else none)
  IO.println s!"{bools} {opts}"
  let u64s : Array UInt64 := #[1, 2, 18446744073709551615]
  let nats := u64s.map (·.toNat + 1)
  IO.println nats
  let pairs := (mkArr 4).map (fun x => (x, s!"{x}"))
  let flags := pairs.map (fun (x, s) => x % 2 == 0 && s.length == 1)
  IO.println s!"{pairs} {flags}"
  let empty : Array Nat := #[]
  IO.println (empty.map (·.toFloat))
  let floats := (mkArr 5).map (·.toFloat.sqrt)
  let bytes := floats.map (·.toUInt8)
  IO.println s!"{floats} {bytes}"
end O7Map

namespace SMapA
-- from rv6/lower/SMapA.lean
/-! Nested map loops (split-map-loops, fd6cf01): representation-changing
maps inside maps, closures capturing loop variables, mapIdx, three levels. -/

@[noinline] def mk (n m : Nat) : Array (Array Nat) :=
  (Array.range n).map fun r => (Array.range m).map fun c => r * 1000 + c

def main : IO Unit := do
  let a := mk 5 4
  -- 1: Nat -> Bool inside Nat-array -> Bool-array
  let b : Array (Array Bool) := a.map (·.map (· % 2 == 0))
  IO.println s!"1 {b}"
  -- 2: Nat -> Float, captured outer row size
  let f : Array (Array Float) := a.map fun row => row.map fun x => x.toFloat / row.size.toFloat
  IO.println s!"2 {f}"
  -- 3: mapIdx outer, inner captures the index
  let g : Array (Array UInt8) := a.mapIdx fun i row => row.map fun x => (x + i).toUInt8
  IO.println s!"3 {g}"
  -- 4: three levels Nat -> String
  let t : Array (Array (Array Nat)) := (Array.range 3).map fun i => (Array.range 3).map fun j => (Array.range 3).map fun k => i*100+j*10+k
  let ts : Array (Array (Array String)) := t.map (·.map (·.map toString))
  IO.println s!"4 {ts}"
  -- 5: three levels Nat -> Float -> UInt64 (inner map result of a map)
  let tf : Array (Array (Array UInt64)) := t.map (·.map fun r => (r.map (·.toFloat * 1.5)).map (·.toUInt64))
  IO.println s!"5 {tf}"
  -- 6: inner array shared (row used after map)
  let rows := a.map fun row => (row.map (·.toFloat), row.size, row)
  IO.println s!"6 {rows.map (·.1)} {rows.map (·.2.1)} {rows.map (·.2.2)}"
  -- 7: outer array shared
  let b2 : Array (Array Int) := a.map (·.map fun (x : Nat) => (x : Int) - 2500)
  IO.println s!"7 {b2} {a}"
  -- 8: empty arrays at each level
  let e1 : Array (Array Nat) := #[#[], #[1], #[]]
  IO.println s!"8 {e1.map (·.map (·.toFloat))} {(#[] : Array (Array Nat)).map (·.map (· == 0))}"
  -- 9: inner map over a captured outer array (not the element)
  let col := #[10, 20, 30]
  let h : Array (Array Float) := a.map fun row => col.map fun c => (c + row.size).toFloat
  IO.println s!"9 {h}"
  -- 10: map of a map inside foldl
  let s := a.foldl (fun acc row => acc + ((row.map (·.toFloat)).foldl (· + ·) 0)) 0.0
  IO.println s!"10 {s}"
  -- 11: map inside List.map inside Array.map
  let l : Array (List (Array Bool)) := a.map fun row => [row, row.reverse].map (·.map (· > 2002))
  IO.println s!"11 {l}"
  -- 12: big Nats (≥ 2^63, ≥ 2^64) nested to Int and back
  let big : Array (Array Nat) := (Array.range 3).map fun i => (Array.range 3).map fun j => 2^63 + i * 2^64 + j
  let bi : Array (Array Int) := big.map (·.map fun (x : Nat) => -(x : Int))
  IO.println s!"12 {bi} {(bi.map (·.map Int.natAbs)) == big}"
  -- 13: map whose function branches (join points) on the outer element
  let br : Array (Array Float) := a.map fun row =>
    if row.size > 3 then row.map (fun x => if x % 3 == 0 then x.toFloat else -x.toFloat)
    else row.map (fun _ => 0.5)
  IO.println s!"13 {br}"
  -- 14: mapFinIdx nested
  let mf : Array (Array UInt16) := a.mapFinIdx fun i row _ => row.mapFinIdx fun j x _ => (x + i * 7 + j).toUInt16
  IO.println s!"14 {mf}"
  -- 15: nested zipWith / map
  let z : Array (Array Float) := (a.zip a.reverse).map fun (r1, r2) => (r1.zip r2).map fun (x, y) => (x + y).toFloat
  IO.println s!"15 {z}"
end SMapA

def main : IO Unit := do
  IO.println "=== O7Map"
  O7Map.main
  IO.println "=== SMapA"
  SMapA.main
