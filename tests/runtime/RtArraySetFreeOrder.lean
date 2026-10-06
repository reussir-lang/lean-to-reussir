/-! Runtime test (review RS10-01 of switch step 10): the order of the
observable releases when an array set replaces the last reference to a
structure. Part 1: a structure of two handles (each handle's text reaches
the shared temporary file when it is closed). Part 2: a structure holding
handles, an array of handles and an unresolved promise whose `sync`
dependent prints. Natively the set releases the old element with
`lean_dec` (`lean_array_uset`), which frees it through the stack of objects:
its last field first. lean2rr's set released the last reference through
the record's own release, which frees the first cell's fields in field
order ("p1a p1b" instead of native's "p1b p1a"); it now frees it inside a
free the runtime starts (`leanrt::drop::release`). -/

structure E where
  a : IO.FS.Handle
  p : IO.Promise Unit
  hs : Array IO.FS.Handle
  b : IO.FS.Handle

structure P where
  a : IO.FS.Handle
  b : IO.FS.Handle

def hnd (path : System.FilePath) (tag : String) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk path .append
  h.putStr s!"{tag} "
  return h

def mkE (path : System.FilePath) (t : String) : IO E := do
  let a ← hnd path s!"{t}a"
  let p ← IO.Promise.new (α := Unit)
  let _ ← IO.mapTask (sync := true) (t := p.result?) fun r => IO.println s!"  dependent {t} ({r.isSome})"
  let h0 ← hnd path s!"{t}h0"
  let h1 ← hnd path s!"{t}h1"
  let b ← hnd path s!"{t}b"
  return { a, p, hs := #[h0, h1], b }

def showFile (path : System.FilePath) : IO Unit := do
  IO.println s!"  file: {← IO.FS.readFile path}"
  IO.FS.writeFile path ""

@[noinline] def setAt (arr : Array E) (i : Nat) (x : E) : Array E := arr.set! i x
@[noinline] def setP (arr : Array P) (i : Nat) (x : P) : Array P := arr.set! i x

def main : IO Unit := do
  let (h0, path) ← IO.FS.createTempFile
  h0.flush
  IO.println "part 1: Array P, set! 0 replaces the last reference to p1"
  let rp ← IO.mkRef (#[] : Array P)
  rp.set #[{ a := ← hnd path "p1a", b := ← hnd path "p1b" }, { a := ← hnd path "p2a", b := ← hnd path "p2b" }]
  let arr ← rp.swap #[]
  let n := { a := ← hnd path "n1a", b := ← hnd path "n1b" }
  let arr := setP arr 0 n
  IO.println s!"  after the set ({arr.size})"
  showFile path
  rp.set arr
  rp.set #[]
  IO.println "  after the free"
  showFile path
  IO.println "part 2: Array E, set! 1 replaces the last reference to e2"
  let r ← IO.mkRef (#[] : Array E)
  r.set #[← mkE path "e1", ← mkE path "e2", ← mkE path "e3"]
  let arr ← r.swap #[]
  let x ← mkE path "x2"
  let arr := setAt arr 1 x
  IO.println s!"  after the set ({arr.size})"
  showFile path
  r.set arr
  r.set #[]
  IO.println "  after the free"
  showFile path
  IO.FS.removeFile path
