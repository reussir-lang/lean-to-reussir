/-! Runtime test: the order in which file handles are closed when a
container holding them is dropped at once (each handle's buffered line
reaches the shared file when it is closed). Native Lean frees through a
stack of objects, last pushed first: an array's last element first, a
nested array's elements before the elements before it, a record's last
field first. The runtime's containers do the same (`leanrt::drop`), and
handles reached through records while a container is freed are closed in
that order too (`RtDropOrderRec` has handles deeper in records). (A list
or structure of handles dropped by itself, with no container, starts with
its first cell's fields in order; plan §10.) -/
@[noinline] def openAll (path : System.FilePath) (tags : List String) : IO (Array IO.FS.Handle) := do
  let mut hs := #[]
  for tag in tags do
    let h ← IO.FS.Handle.mk path .append
    h.putStr s!"{tag}\n"
    hs := hs.push h
  return hs

structure Two where
  a : IO.FS.Handle
  b : IO.FS.Handle

@[noinline] def dropTwos (xs : Array Two) : Nat := xs.size
@[noinline] def dropThunks (xs : Array (Thunk IO.FS.Handle)) : Nat := xs.size
@[noinline] def dropOpts (xs : Array (Option IO.FS.Handle)) : Nat := xs.size
@[noinline] def dropArr (hs : Array IO.FS.Handle) : Nat := hs.size
@[noinline] def dropNested (hs : Array (Array IO.FS.Handle)) : Nat := hs.size

def main : IO Unit := do
  let dir : System.FilePath := "dd2-tmp"
  IO.FS.createDirAll dir
  let f1 := dir / "arr.txt"
  IO.FS.writeFile f1 ""
  IO.println s!"arr {dropArr (← openAll f1 ["a1", "a2", "a3"])}"
  IO.print (← IO.FS.readFile f1)
  let f4 := dir / "nested.txt"
  IO.FS.writeFile f4 ""
  let x ← openAll f4 ["n1", "n2"]
  let y ← openAll f4 ["n3", "n4"]
  IO.println s!"nested {dropNested #[x, y]}"
  IO.print (← IO.FS.readFile f4)
  let f5 := dir / "twos.txt"
  IO.FS.writeFile f5 ""
  let hs ← openAll f5 ["s1a", "s1b", "s2a", "s2b"]
  match hs.toList with
  | [a1, b1, a2, b2] => IO.println s!"twos {dropTwos #[⟨a1, b1⟩, ⟨a2, b2⟩]}"
  | _ => pure ()
  IO.print (← IO.FS.readFile f5)
  let f6 := dir / "thunks.txt"
  IO.FS.writeFile f6 ""
  let hs ← openAll f6 ["k1", "k2", "k3"]
  IO.println s!"thunks {dropThunks (hs.map fun h => Thunk.pure h)}"
  IO.print (← IO.FS.readFile f6)
  let f7 := dir / "opts.txt"
  IO.FS.writeFile f7 ""
  let hs ← openAll f7 ["o1", "o2", "o3"]
  IO.println s!"opts {dropOpts (hs.map some)}"
  IO.print (← IO.FS.readFile f7)
  IO.FS.removeDirAll dir
