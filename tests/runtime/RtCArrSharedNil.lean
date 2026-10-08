/-! Runtime test (compact scalar arrays, hunt HCA-01): mono CSE shares one
value without an array between uses at different types: `let _x : List
(Array UInt8) := List.nil ◾` (typed at its first use) is also passed where
a `List (Array Float)` or `List (Array UInt64)` is expected (the
accumulators of `List.map`). Such a value (a constructor whose fields are
erased or hold no array) holds no array, so it is no crossing
(docs/implementation/representations/compact-arrays.md, "The
whole-program check turns a kind off"). Before, it turned u8 and f64 off;
now every kind stays on (`L2R_DEBUG=1`). Also `Option.none` and
`Except.error` beside values of the same types that hold compact arrays. -/
@[noinline] def bs : List (List UInt8) := [[1, 2], [3], []]
@[noinline] def fs : List (List Float) := [[1.5], [2.5, 3.5]]
@[noinline] def us : List (List UInt64) := [[0x8000000000000000], []]

@[noinline] def pickO (b : Bool) : Option (Array UInt8) := if b then some #[9, 8] else none
@[noinline] def pickF (b : Bool) : Option (Array Float) := if b then some #[9.5] else none

@[noinline] def errOrU8 (b : Bool) : Except String (Array UInt8) := if b then .ok #[1, 255] else .error "no u8"
@[noinline] def errOrF (b : Bool) : Except String (Array Float) := if b then .ok #[1.25] else .error "no f64"

def showE {α : Type} [ToString α] : Except String α → String
  | .ok a => toString a
  | .error e => e

def main : IO Unit := do
  let a : List (Array UInt8) := bs.map List.toArray
  let b : List (Array Float) := fs.map List.toArray
  let c : List (Array UInt64) := us.map List.toArray
  IO.println s!"{a.map (·.toList)} {b.map (·.toList)} {c.map (·.toList)}"
  IO.println s!"{(pickO true).map (·.toList)} {(pickO false).map (·.toList)}"
  IO.println s!"{(pickF true).map (·.toList)} {(pickF false).map (·.toList)}"
  IO.println s!"{showE (errOrU8 false)} {showE (errOrF false)} {showE (errOrU8 true)} {showE (errOrF true)}"
