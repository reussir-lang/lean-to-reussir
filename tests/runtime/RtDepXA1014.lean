/-! Runtime test: case `A1014` of the shared dependent-type corpus (programs
built by another translator's team and checked against native Lean). It
checks: `List (List ι)` values whose inner lists are shared (one list
replicated) and whose tails are shared across lists (`l_i = i :: l_{i-1}`),
converted through the memo's two list loops: ... Small size (3). -/
@[noinline] def lens (h : {ι : Type} → List (List ι) → Nat) (a : List (List Nat)) (b : List (List String)) : Nat :=
  h a + h b

/-- `[l_n, …, l_1]` with `l_i = i :: l_{i-1}`: the lists share their tails. -/
def tails {α : Type} (f : Nat → α) (n : Nat) : List (List α) := Id.run do
  let mut l : List α := []
  let mut out : List (List α) := []
  for i in [0:n] do
    l := f i :: l
    out := l :: out
  return out

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 1000
  let inner := List.range 1000
  let rep := List.replicate n inner
  IO.println (lens (fun l => l.length + (l.headD []).length) rep (List.replicate n (inner.map toString)))
  IO.println (lens (fun l => l.length + (l.headD []).length) (tails id n) (tails toString n))
