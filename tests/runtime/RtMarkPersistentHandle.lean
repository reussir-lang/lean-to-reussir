/-! Runtime test (`NAME.pipe` prints the files after the exit):
`Runtime.markPersistent` makes its argument persistent, as native
`lean_mark_persistent` does (it sets the count to 0, and a persistent
object is never freed). So a file handle marked persistent and then dropped
is not closed: its buffered bytes are not in the file yet, and reach it at
the exit. A handle itself, a handle in a structure, and a handle at a type
parameter; the program makes no task, so no walk runs. Before the fix
lean2rr released the marked value as any other: the handle was closed at
its last reference and its bytes written at once (review RV-03 of
HTSK2-02). -/
structure Log where
  name : String
  h : IO.FS.Handle

@[noinline] unsafe def markGen {α : Type} (x : α) : IO α := Runtime.markPersistent x

@[noinline] unsafe def direct (path : String) : IO Unit := do
  let h ← IO.FS.Handle.mk path .write
  let h ← Runtime.markPersistent h
  h.putStr "direct bytes"

@[noinline] unsafe def inStruct (path : String) : IO Unit := do
  let l ← Runtime.markPersistent ({ name := "log", h := ← IO.FS.Handle.mk path .write } : Log)
  l.h.putStr s!"{l.name} bytes"

@[noinline] unsafe def generic (path : String) : IO Unit := do
  let h ← markGen (← IO.FS.Handle.mk path .write)
  h.putStr "generic bytes"

unsafe def main : IO Unit := do
  direct "mp-direct.txt"
  inStruct "mp-struct.txt"
  generic "mp-generic.txt"
  for f in ["mp-direct.txt", "mp-struct.txt", "mp-generic.txt"] do
    IO.println s!"{f} after drop: {repr (← IO.FS.readFile f)}"
