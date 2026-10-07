/-! Runtime test: a typed reference to a list modified by uniform code
(blowup audit BA-10). `Sink` stores an `IO.Ref (List α)` with `α` a field;
`Sink.push` modifies the reference at `List lcAny` while the cell holds a
`List Nat`: the reference glue converts the list to the uniform layout to
take it and converts the result back to store it (`genRefFn`,
Lower/Externs.lean), two whole-list conversions per `modify` (64016000
cells for 8000 pushes). Natively `modify` takes the list out of the cell
and conses in place: O(1). The values and the aliasing are correct; the
output is checked here, the allocations by tests/runtime/alloc-check.sh
(RtReprRefUniform.alloc). -/
structure Sink where
  α : Type
  r : IO.Ref (List α)
  x : α

@[noinline] def Sink.push (s : Sink) : IO Unit := s.r.modify (s.x :: ·)

def main (args : List String) : IO Unit := do
  let n := (args.headD "300").toNat!
  let r ← IO.mkRef ([] : List Nat)
  for i in [0:n] do
    Sink.push ⟨Nat, r, i⟩
  let xs ← r.get
  IO.println s!"{xs.length} {xs.headD 0}"
