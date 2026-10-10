/-! Runtime test (`NAME.pipe` prints the file after the exit): as
RtPersistInitHandle, with the file handle held by the initializer's
reference directly (a reference holds its value as a box). In a program
that creates tasks the walk after the initializer marks the reference and
the handle the box points to (a payload whose type cannot hold a task is
marked without being looked into), so the handle stays open when `main`
sets the reference to another handle, as natively: its bytes reach the
file at the exit. Before, the walk marked a box's payload only when the
payload's type could hold a task, so the handle was closed at once
(review RS-01 of the persistent walk). -/
axiom handleNonempty : Nonempty IO.FS.Handle
instance : Nonempty IO.FS.Handle := handleNonempty

initialize logRef : IO.Ref IO.FS.Handle ← do
  let h ← IO.FS.Handle.mk "persist-init-direct.txt" .write
  h.putStr "from-init"
  IO.mkRef h

def main (args : List String) : IO Unit := do
  let t ← IO.asTask (pure args.length)
  let h2 ← IO.FS.Handle.mk "persist-init-other.txt" .write
  logRef.set h2
  IO.println s!"file after set: {repr (← IO.FS.readFile "persist-init-direct.txt")}"
  IO.println s!"task: {(← IO.wait t).toOption}"
