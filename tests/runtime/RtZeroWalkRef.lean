/-! Runtime test: `IO.Ref.modify` leaves a placeholder in the reference
while it updates it (`ST.Ref.take`), and a closed term holding that
reference (`#[r, r, r]`) is first evaluated then, while another task is
unfinished, so its walk for tasks reaches the placeholder. For a type built
only through a cycle of tasks (`structure S where h : Nat; t : Task S`),
the placeholder holds a never-forced `pending` task cell: the walk must not
run it (natively the placeholder is `box(0)`, which the walk skips).
`RtZeroWalkRefNoCache` is the same program with `placeholder-cache` off,
where running the cell built a new placeholder each time, without end.
From the round-9 review of RV9C-01 (C01R-03, repro R10Walk). -/
structure S where
  h : Nat
  t : Task S

axiom S.nonempty : Nonempty S
instance : Nonempty S := S.nonempty

def mkS (n : Nat) : IO S := do
  let p ← IO.Promise.new (α := S)
  let s : S := ⟨n, p.result!⟩
  p.resolve s
  return s

initialize r : IO.Ref S ← IO.mkRef (unsafe (unsafeCast () : S))

@[noinline] def count (a : Array (IO.Ref S)) (s : S) : Nat := a.size + s.h

@[noinline] def refs : Array (IO.Ref S) := #[r, r]

def main (args : List String) : IO Unit := do
  let w := (args.head? >>= String.toNat?).getD 0
  r.set (← mkS 1)
  let bg ← IO.asTask (do IO.sleep 300; pure (7 + w))
  r.modify fun s => { s with h := s.h + count #[r, r, r] s + w }
  IO.println s!"ref {(← r.get).h} {(← r.get).t.get.h} {(← (refs.getD 0 r).get).h}"
  IO.println s!"bg {match bg.get with | .ok v => v | .error _ => 0}"
