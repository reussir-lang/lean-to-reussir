/-! Runtime test (audit Q6 of the destructor port; review RA-01): an
unresolved promise in a record that user code frees while another member
of the record, a list holding a second promise, is still to be released.
`mk` (not inlined) builds the `Holder` and `consume` (not inlined) reads
it, so the record exists and `main` drops it.

Natively `main` frees it with `lean_dec`, which frees a cell's fields last
first: `p` goes first, and its `sync` dependent runs inside the free (`p
start`, the length of a fresh list that it frees itself, `p end`); then
the list `qs` and its promise `q` (`q`). With lean2rr, Reussir's glue
frees a record that user code drops first field first, and each promise
is resolved where the glue reaches it, its dependents run at once: `q`
before `p start` (plan §10, the order of releases in a free that user
code starts; RtPromiseDropRecordPending.l2r.out). The free inside `p`'s
dependent is a free of its own in both. -/

structure Holder where
  qs : List (IO.Promise Unit)
  p  : IO.Promise Unit

@[noinline] def mk (q p : IO.Promise Unit) : Holder := { qs := [q], p := p }

@[noinline] def consume (h : Holder) : IO Unit := do
  IO.println s!"consume {h.qs.length}"

def main (args : List String) : IO Unit := do
  let q ← IO.Promise.new
  let p ← IO.Promise.new
  let _ ← IO.mapTask (sync := true) (t := q.result?) fun _ => IO.println "q"
  let _ ← IO.mapTask (sync := true) (t := p.result?) fun _ => do
    IO.println "p start"
    -- a fresh list, freed when the dependent is done with it
    let xs := List.replicate (args.length + 3) 0
    IO.println s!"{xs.length}"
    IO.println "p end"
  consume (mk q p)
  IO.println "main after"
