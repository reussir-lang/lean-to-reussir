/-! Runtime test: the placeholder of a type whose values can only be built
through a cycle of tasks (`structure S where h : Nat; t : Task S`, made
here with a promise) holds a task cell that is never forced. It is kept in
a once-cell when first built (by `Array.map`, `Array.modify`,
`IO.Ref.modify`), while another task is unfinished: it must not be walked
for its tasks like a constant (natively a placeholder is `box(0)`, which
`lean_mark_persistent` never sees), else the walk runs that cell, which
asks for the placeholder being built, and the program hangs.
From the round-9 review of RV9C-01 (C01R-01, repro R2Task). -/
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

def main (args : List String) : IO Unit := do
  let w := (args.head? >>= String.toNat?).getD 0
  let a ← mkS 1
  let b ← mkS 5
  let bg := Task.spawn fun _ => (List.range (1000 + w)).foldl (· + ·) 0
  if w == 0 || w == 1 then
    let ss := #[a, b].map fun s => { s with h := s.h + 10 }
    IO.println s!"map {ss.map (·.h)} {ss.map (·.t.get.h)}"
  if w == 0 || w == 2 then
    let ss := #[a, b].modify 1 fun s => { s with h := s.h * 3 }
    IO.println s!"modify {ss.map (·.h)}"
  if w == 0 || w == 3 then
    let r ← IO.mkRef a
    r.modify fun s => { s with h := s.h + 1 }
    IO.println s!"ref {(← r.get).h} {(← r.get).t.get.h}"
  IO.println s!"bg {bg.get}"
