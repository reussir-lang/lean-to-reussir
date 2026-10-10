/-! Runtime test (`NAME.pipe` prints the files after the exit):
`Runtime.markPersistent` of a reference that holds a file handle, in a
program that creates tasks, then the reference is set to another value.
Natively the handle is persistent (marked with the reference) and never
closed, so its file is still empty; its bytes reach the file at the exit.
The walk marks the reference and what its box points to: the handle
itself (a payload whose type cannot hold a task is marked without being
looked into), or the `some` cell around it. Before, the walk marked a
box's payload only when the payload's type could hold a task, so the
handle held directly was closed when the reference was set (review RS-01
of the persistent walk). -/
unsafe def main (args : List String) : IO Unit := do
  let t ← IO.asTask (pure args.length)
  let h ← IO.FS.Handle.mk "mp-ref-direct.txt" .write
  h.putStr "direct bytes"
  let r ← IO.mkRef h
  let r ← Runtime.markPersistent r
  r.set (← IO.FS.Handle.mk "mp-ref-other.txt" .write)
  let h2 ← IO.FS.Handle.mk "mp-ref-option.txt" .write
  h2.putStr "option bytes"
  let r2 ← IO.mkRef (some h2)
  let r2 ← Runtime.markPersistent r2
  r2.set none
  IO.println s!"direct: {repr (← IO.FS.readFile "mp-ref-direct.txt")}"
  IO.println s!"option: {repr (← IO.FS.readFile "mp-ref-option.txt")}"
  IO.println s!"task: {(← IO.wait t).toOption}"
