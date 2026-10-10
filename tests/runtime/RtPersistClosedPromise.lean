/-! Runtime test: a closed term evaluated lazily (`lean_obj_once`) whose
value is a promise that a dedicated task it starts resolves after 150 ms.
Natively the term's first evaluation marks it persistent
(`lean_mark_persistent`), which waits for the promise's result task: the
resolver prints its line before `main` reads the term, and `main` sees the
promise resolved. `result?` is taken inside a function, so it is no
closed term itself. Before HTSK2-02's fix lean2rr's walk did not look into
a promise: `main` saw it unresolved, before the resolver's line (review
RV-02 of HTSK2-02: a closed term can reach a promise, not only
`Runtime.markPersistent`). -/
@[noinline] unsafe def mkP (_u : Unit) : IO.Promise Nat := unsafeBaseIO do
  let p ← IO.Promise.new (α := Nat)
  let _ ← IO.asTask (prio := .dedicated) do
    IO.sleep 150
    IO.println "resolver: resolving"
    p.resolve 5
  let _ ← (IO.println "mkP: task started").toBaseIO
  pure p

@[noinline] def finished (p : IO.Promise Nat) : BaseIO Bool := IO.hasFinished p.result?

unsafe def main (args : List String) : IO Unit := do
  IO.println s!"start {args.length}"
  let p := mkP ()
  let fin ← finished p
  IO.println s!"main: made, resolved: {fin}"
