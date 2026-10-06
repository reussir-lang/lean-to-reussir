/-! Runtime test (review RS10-01 of switch step 10): `Array.pop` releasing
the last reference to a structure of two handles (each handle's text
reaches the shared temporary file when it is closed). Natively
`lean_array_pop` releases it with `lean_dec`: its last field first, as
`RtArraySetFreeOrder` for a set. -/

structure P where
  a : IO.FS.Handle
  b : IO.FS.Handle

def hnd (path : System.FilePath) (tag : String) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk path .append
  h.putStr s!"{tag} "
  return h

@[noinline] def popP (arr : Array P) : Array P := arr.pop

def main : IO Unit := do
  let (h0, path) ← IO.FS.createTempFile
  h0.flush
  let rp ← IO.mkRef (#[] : Array P)
  rp.set #[{ a := ← hnd path "p1a", b := ← hnd path "p1b" }, { a := ← hnd path "p2a", b := ← hnd path "p2b" }]
  let arr ← rp.swap #[]
  let arr := popP arr
  IO.println s!"after the pop ({arr.size})"
  IO.println s!"file: {← IO.FS.readFile path}"
  IO.FS.writeFile path ""
  rp.set arr
  rp.set #[]
  IO.println s!"after the free: {← IO.FS.readFile path}"
  IO.FS.removeFile path
