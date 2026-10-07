/-! Runtime test: a reference set that is the reference's last use (each
handle's text reaches the shared temporary file when it is closed).
Natively `ST.Ref.set` borrows the reference (`@&`): `lean_st_ref_set`
stores the new value and releases the old one, and then the caller
releases the reference, which frees the new value: the old value's handles
are closed first ("old.b old.a new.b new.a"). lean2rr's `l2r_rc_set` took
the reference's cell, and the cell's last use was the store, so the cell
was released there, before the old value's release: the new value was
freed first ("new.b new.a old.b old.a"; runtime/README.md, Requests for
lean2rr 33, on the branch that added this test). `l2r_rc_set_ref` now also
takes the reference and releases it after the old value. -/

structure P where
  a : IO.FS.Handle
  b : IO.FS.Handle

def hnd (path : System.FilePath) (tag : String) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk path .append
  h.putStr s!"{tag} "
  return h

def setLast (path : System.FilePath) : IO Unit := do
  let r ← IO.mkRef ({ a := ← hnd path "old.a", b := ← hnd path "old.b" } : P)
  r.set { a := ← hnd path "new.a", b := ← hnd path "new.b" }

def main : IO Unit := do
  let (h0, path) ← IO.FS.createTempFile
  h0.flush
  setLast path
  IO.println s!"file: {← IO.FS.readFile path}"
  IO.FS.removeFile path
