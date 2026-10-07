/-! Runtime test: case `A1010` of the shared dependent-type corpus (programs
built by another translator's team and checked against native Lean). It
checks: A nested list of 10^6 cells converted through the memo's two list
loops, stack-safe whatever chapter 04's verdict on the list. Small size (5).
-/
@[noinline] def lens (h : {ι : Type} → List (List ι) → Nat) (a : List (List Nat)) (b : List (List String)) : Nat :=
  h a + h b

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 1000
  IO.println (lens (fun l => l.length + (l.headD []).length) [List.range n, List.range 3] [(List.range n).map toString])
