/-! Runtime test (`NAME.pipe` prints the file after the exit): in a program
that creates tasks, an initializer's result is walked after the
initializer, and the walk marks the cells it visits persistent: here the
reference and the `some` cell it holds (an `Option`'s field is a `Box`,
which can hold a task in such a program). A persistent cell is never
freed, so the file handle in the `some` cell stays open when `main` sets
the reference to `none`, as natively (the module initializer marks the
result persistent): its bytes reach the file at the exit. Before the
walk of initializer results lean2rr closed the handle at once (hunt
HSG-02's example, now as native in a program with tasks; without tasks
nothing is walked, docs/implementation/startup/constants.md). -/
initialize logRef : IO.Ref (Option IO.FS.Handle) ← do
  let h ← IO.FS.Handle.mk "persist-init-h.txt" .write
  h.putStr "from-init"
  IO.mkRef (some h)

def main (args : List String) : IO Unit := do
  let t ← IO.asTask (pure args.length)
  logRef.set none
  IO.println s!"file after set none: {repr (← IO.FS.readFile "persist-init-h.txt")}"
  IO.println s!"task: {(← IO.wait t).toOption}"
