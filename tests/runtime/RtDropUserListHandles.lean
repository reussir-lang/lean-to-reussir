/-! Runtime test (tests for the destructor port): the order of the closes
when user code drops a list of handles by itself, with no container
around it. `build` (not inlined) opens 8 handles on one file in append
mode, writes the tags `1` to `8` with them, and returns the list
`[h1, …, h8]`. The output is buffered, so a tag reaches the file only
when its handle is closed: the file shows the order of the closes.
`main` passes the list to `ignore`, a call that is not inlined and does
not look at it, and then drops the list.

Natively `main` does not know the list's constructor, so it calls
`lean_dec`. A free decrements every field of a cell, pushes each field
whose count reaches zero, and then frees the last pushed first
(`lean_del_core` and `lean_dec_ref_cold`): the first cell pushes `h1`,
then the second cell; the second cell is popped first and pushes `h2`,
then the third cell; and so on. The handles are therefore closed from the
back: `87654321`.

What the test pins: the order policy of a free that starts in user code.
A list drop that releases the head, frees the cell and then goes on to
the tail (Reussir's drop glue), with each close done at once, closes the
handles from the front (`12345678`). -/

def path : System.FilePath := "dul-tmp.txt"

@[noinline] def openW (tag : String) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk path .append
  h.putStr tag
  pure h

@[noinline] def build : IO (List IO.FS.Handle) := do
  let mut hs := []
  for i in [0:8] do
    hs := (← openW s!"{8 - i}") :: hs
  pure hs

@[noinline] def ignore (_ : List IO.FS.Handle) : Nat := 8

def main : IO Unit := do
  IO.FS.writeFile path ""
  IO.println s!"ignored {ignore (← build)}"
  IO.println s!"list {← IO.FS.readFile path}"
  IO.FS.removeFile path
