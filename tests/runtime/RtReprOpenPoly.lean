/-! Runtime test: a structure field that is a generic function (`run :
{α : Type} → List α → Nat`) called with typed lists (blowup audit BA-15).
The stored function is the instance at `lcAny` (it takes a list of
`L2RBox`es), so every call with a `List Nat` converts the list first: O(n)
per call for a function that only tests for emptiness, O(n^2) in the loop
(32016000 cells at n = 4000; natively O(1) per call). The output is
checked here; the allocations by tests/runtime/alloc-check.sh
(RtReprOpenPoly.alloc). -/
structure Op where
  run : {α : Type} → List α → Nat

@[noinline] def isNonEmpty {α : Type} : List α → Nat
  | [] => 0
  | _ :: _ => 1

def ops : List Op := [⟨isNonEmpty⟩, ⟨fun xs => 2 * isNonEmpty xs⟩]

def main (args : List String) : IO Unit := do
  let n := (args.headD "300").toNat!
  let xs := List.range n
  let mut acc := 0
  for i in [0:n] do
    for o in ops do
      acc := acc + o.run (i :: xs)
  IO.println acc
