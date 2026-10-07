/-! Runtime test (Reussir patch 13-d, issue 13; review of 13-d): the order
of the closes when a free reaches a structure whose last record field is
followed by a field that pushes its own free (an array, a thunk), three
cells below the start of the free (the array, then `E`, then `W`). Each
scenario puts `E x` (a handle, then `W x`: a handle, then `x`) into an
array held by an `IO.Ref` and frees the array with `r.set #[]`; each
handle writes its tag to the scenario's file when it is closed. Natively
`lean_del` pushes a cell's fields in order and pops the last first: in
`x`, the array (or thunk) goes before the record field. Without 13-d,
Reussir's glue for `x` (`drop_and_free`) released the record field after
the cell, directly, before the free the later field had pushed: T1 closed
`i.b i.a arr1 arr0`, natively `arr1 arr0 i.b i.a`. -/

def hnd (p : System.FilePath) (tag : String) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk p .append
  h.putStr s!"{tag} "
  return h

structure In where
  a : IO.FS.Handle
  b : IO.FS.Handle

def mkIn (p : System.FilePath) (t : String) : IO In := do
  let a ← hnd p s!"{t}.a"
  let b ← hnd p s!"{t}.b"
  return { a, b }

def mkArr (p : System.FilePath) (t : String) : IO (Array IO.FS.Handle) := do
  return #[← hnd p s!"{t}0", ← hnd p s!"{t}1"]

structure W (α : Type) where
  h : IO.FS.Handle
  x : α

structure E (α : Type) where
  h : IO.FS.Handle
  w : W α

@[noinline] def scenario {α : Type} (name : String) (mk : System.FilePath → IO α) : IO Unit := do
  let (h0, path) ← IO.FS.createTempFile
  h0.flush
  let r ← IO.mkRef (#[] : Array (E α))
  let x ← mk path
  let w : W α := { h := ← hnd path "w.h", x }
  let e : E α := { h := ← hnd path "e.h", w }
  r.set #[e]
  r.set #[]
  IO.println s!"{name}: {← IO.FS.readFile path}"
  IO.FS.removeFile path

-- T1: a record, then an array
structure X1 where
  i : In
  arr : Array IO.FS.Handle
-- T4: a record, then a thunk of a handle (a thunk cell)
structure X4 where
  i : In
  t : Thunk IO.FS.Handle
-- T9: a variant whose arm has a record, then an array
inductive X9 where
  | a (i : In) (arr : Array IO.FS.Handle)
  | b (i : In) (h : IO.FS.Handle)
-- T14: an Option of a record, then an array
structure X14 where
  o : Option In
  arr : Array IO.FS.Handle

def main : IO Unit := do
  scenario "T1 " fun p => do return ({ i := ← mkIn p "i", arr := ← mkArr p "arr" } : X1)
  scenario "T4 " fun p => do return ({ i := ← mkIn p "i", t := Thunk.pure (← hnd p "t") } : X4)
  scenario "T9a" fun p => do return X9.a (← mkIn p "i") (← mkArr p "arr")
  scenario "T14" fun p => do return ({ o := some (← mkIn p "o"), arr := ← mkArr p "arr" } : X14)
