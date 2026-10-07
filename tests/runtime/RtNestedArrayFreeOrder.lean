/-! Runtime test (review RS11-01 of switch step 11): the order of the closes
when a free reaches a structure whose last field is an array, below the
record that is freed (each handle's text reaches the shared temporary file
when it is closed). `S` = an `In` (two handles), then an `Array` of two
handles; `W` = a handle, then an `S`; `V` = a handle, then a `W`. Natively
`lean_del` pushes a cell's fields in order and pops the last first:
freeing a `V` closes `w.arr1 w.arr0 w.i.b w.i.a w.h h`.
- The free of the array (second part): Reussir's glue for a cell below the
  first one (local patch 13-b, `drop_and_free`) released the cell's last
  record field (`i`) after the cell, directly, while the array had already
  pushed its free: `i`'s handles closed before the array's
  (`w.i.b w.i.a w.arr1 w.arr0 w.h h`). Reussir patch 13-d (issue 13)
  keeps that field for last only when no later field pushes work;
  scripts/l2r.py requires it.
- The `Array.set!` (first part): on dev an `Array V` held the `V` records
  themselves, and the set dropped the old `V` through the record's own
  release, which frees the first cell's fields in field order (`v1.h`
  first). With one representation per `Array α` (rule 1) the array holds
  boxes (the one-word `LAny`): the last release of a boxed record goes
  through leanrt's drop worklist (`release_last`: the record's cell, as
  one pending cell), which runs
  the program's release of the record (`l2r_any_rel_<n>_c`) inside a free, so
  its fields go onto the pending stack and close last first, as natively
  (translation plan §10, "Order of releases in one free"). -/

structure In where
  a : IO.FS.Handle
  b : IO.FS.Handle

structure S where
  i : In
  arr : Array IO.FS.Handle

structure W where
  h : IO.FS.Handle
  s : S

def hnd (path : System.FilePath) (tag : String) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk path .append
  h.putStr s!"{tag} "
  return h

def mkW (path : System.FilePath) (t : String) : IO W := do
  let i : In := { a := ← hnd path s!"{t}.i.a", b := ← hnd path s!"{t}.i.b" }
  let arr := #[← hnd path s!"{t}.arr0", ← hnd path s!"{t}.arr1"]
  return { h := ← hnd path s!"{t}.h", s := { i, arr } }

structure V where
  h : IO.FS.Handle
  w : W

@[noinline] def setV (arr : Array V) (i : Nat) (x : V) : Array V := arr.set! i x

def mkV (path : System.FilePath) (t : String) : IO V := do
  let w ← mkW path s!"{t}.w"
  return { h := ← hnd path s!"{t}.h", w }

def main : IO Unit := do
  let (h0, path) ← IO.FS.createTempFile
  h0.flush
  let r ← IO.mkRef (#[] : Array V)
  r.set #[← mkV path "v1"]
  let arr ← r.swap #[]
  let arr := setV arr 0 (← mkV path "n1")
  IO.println s!"after the set ({arr.size})"
  IO.println s!"  file: {← IO.FS.readFile path}"
  IO.FS.writeFile path ""
  r.set arr
  r.set #[]
  IO.println "after the free"
  IO.println s!"  file: {← IO.FS.readFile path}"
  IO.FS.removeFile path
