/-! Runtime test: the order of the observable releases when one release
frees an array of structures (`r.set #[]` on the reference that holds the
only reference to it). Each structure holds file handles (buffered output
to one temporary file, written with `putStr` and never flushed, so each
handle's text reaches the file when it is closed), an array of handles, and
an unresolved promise whose `sync` dependent prints. Natively the free goes
through one stack of objects, last pushed first: the array from its last
element, a structure's last field first, a nested array's elements before
the fields before it; each dependent runs when the free reaches its
promise. lean2rr frees through one stack of pending work too
(`leanrt::drop`, Reussir's glue), and resolves the promises after the free,
in the order the free reached them (`task::defer_promise_drop`), before the
code after the release goes on. So the file shows Lean's close order, and
the dependents print in Lean's order, before "after the free".

This pins the shape against a release of the elements one by one outside
the free's stack (an element whose count is 1 released directly): Reussir's
glue releases the fields of a structure it starts a free at in field order
(plan §10), and each element would be a free of its own. Part 2 shares one
element with another reference (the array's free only decrements it; the
reference's release frees it later), part 3 nests the structures in an
array field. -/

structure E where
  a : IO.FS.Handle
  p : IO.Promise Unit
  hs : Array IO.FS.Handle
  b : IO.FS.Handle

structure F where
  tag : String
  es : Array E
  h : IO.FS.Handle

def hnd (path : System.FilePath) (tag : String) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk path .append
  h.putStr s!"{tag} "
  return h

/-- An element: handles `<t>a`, `<t>h0`, `<t>h1`, `<t>b`, and a promise
whose dependent prints `dependent <t>`. -/
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

def part1 (path : System.FilePath) : IO Unit := do
  IO.println "part 1: #[e1, e2, e3]"
  let r ← IO.mkRef (#[] : Array E)
  r.set #[← mkE path "e1", ← mkE path "e2", ← mkE path "e3"]
  r.set #[]
  IO.println "  after the free"
  showFile path

def part2 (path : System.FilePath) : IO Unit := do
  IO.println "part 2: #[e1, e2, e3], e2 also held by another reference"
  let r ← IO.mkRef (#[] : Array E)
  let keep ← IO.mkRef (none : Option E)
  let e2 ← mkE path "e2"
  keep.set (some e2)
  r.set #[← mkE path "e1", e2, ← mkE path "e3"]
  r.set #[]
  IO.println "  after the free"
  showFile path
  keep.set none
  IO.println "  after the other release"
  showFile path

def part3 (path : System.FilePath) : IO Unit := do
  IO.println "part 3: #[f1, f2], each with an array of two elements"
  let r ← IO.mkRef (#[] : Array F)
  let f1 := { tag := "f1", es := #[← mkE path "f1e1", ← mkE path "f1e2"], h := ← hnd path "f1h" }
  let f2 := { tag := "f2", es := #[← mkE path "f2e1", ← mkE path "f2e2"], h := ← hnd path "f2h" }
  r.set #[f1, f2]
  r.set #[]
  IO.println "  after the free"
  showFile path

def main : IO Unit := do
  let (h0, path) ← IO.FS.createTempFile
  h0.flush
  part1 path
  part2 path
  part3 path
  IO.FS.removeFile path
