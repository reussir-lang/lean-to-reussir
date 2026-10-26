/-! Runtime test (tests for the destructor port): the order of the closes
when a list of handles is freed by the runtime. `build` (not inlined)
opens 8 handles on one file in append mode, writes the tags `1` to `8`
with them, and returns the list `[h1, …, h8]`. The output is buffered,
so a tag reaches the file only when its handle is closed: the file shows
the order of the closes. `report` prints the file and empties it.

- `ref`: the list is put in an `IO.Ref`, which is then set to `[]`
  (`lean_st_ref_set` frees the old value).
- `arr`: the list is the element of a one-element array, which `clear`
  (not inlined) replaces with `[]` (`Array.set!` frees the old element).

Natively the runtime calls `lean_dec` on the list. A free decrements
every field of a cell, pushes each field whose count reaches zero, and
then frees the last pushed first (`lean_del_core` and
`lean_dec_ref_cold`): the first cell pushes `h1`, then the second cell;
the second cell is popped first and pushes `h2`, then the third cell;
and so on. The handles are therefore closed from the back: `87654321`
in each part.

What the test pins: a free that starts in the runtime keeps native's
order through the cells of a list, also when the list's own drop (Reussir's
drop glue) releases the head, frees the cell and then goes on to the
tail: the runtime pushes each close and pops the last pushed first.
`RtDropUserListHandles` has the same list dropped by user code. -/

def path : System.FilePath := "drl-tmp.txt"

@[noinline] def openW (tag : String) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk path .append
  h.putStr tag
  pure h

@[noinline] def build : IO (List IO.FS.Handle) := do
  let mut hs := []
  for i in [0:8] do
    hs := (← openW s!"{8 - i}") :: hs
  pure hs

@[noinline] def clear (a : Array (List IO.FS.Handle)) : Array (List IO.FS.Handle) := a.set! 0 []

def report (tag : String) : IO Unit := do
  IO.println s!"{tag} {← IO.FS.readFile path}"
  IO.FS.writeFile path ""

def main : IO Unit := do
  IO.FS.writeFile path ""
  let r ← IO.mkRef ([] : List IO.FS.Handle)
  r.set (← build)
  r.set []
  report "ref"
  IO.println s!"arr size {(clear #[← build]).size}"
  report "arr"
  IO.FS.removeFile path
