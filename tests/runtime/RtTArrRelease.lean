/-! Runtime test (typed arrays, clean step B1): element types whose values
can hold something whose release the program can observe stay boxed. A
typed array releases its elements in another order than native Lean when
elements or their members are shared, and releases a record that a set
replaces by its own drop (its fields in field order); with a handle in the
element that would change the order in which files close. Here: records
holding a file handle (`Res`), a closure (`Cb`) and a task (`Job`), each in
an array that is updated by `set!` and `pop` and then dropped whole while
handles are shared between elements; the files are read back after each
step. An `Array String` beside them stays typed. `RtTArrRelease.l2r-debug`
checks the kinds and the reasons. The files are made in the current
directory and removed at the end. -/

structure Res where
  name : String
  h : IO.FS.Handle

structure Cb where
  name : String
  f : Nat → Nat

structure Job where
  id : Nat
  t : Task Nat

def readAll (names : List String) : IO String := do
  let mut out := ""
  for n in names do
    out := out ++ s!"{n}=[{(← IO.FS.readFile n).trim}] "
  return out

@[noinline] def stepRes (rs : Array Res) (i : Nat) (r : Res) : Array Res := rs.set! i r

def main : IO Unit := do
  let names := ["tarr-rel-a.txt", "tarr-rel-b.txt", "tarr-rel-c.txt"]
  let ha ← IO.FS.Handle.mk names[0]! .write
  let hb ← IO.FS.Handle.mk names[1]! .write
  let hc ← IO.FS.Handle.mk names[2]! .write
  -- shared handles: element 3 shares a's handle, element 4 shares b's
  let mut rs : Array Res := #[⟨"a", ha⟩, ⟨"b", hb⟩, ⟨"c", hc⟩, ⟨"a2", ha⟩, ⟨"b2", hb⟩]
  for r in rs do
    r.h.putStr s!"{r.name};"
  rs := stepRes rs 2 ⟨"c3", ha⟩
  rs := rs.pop
  IO.println s!"res {rs.map (·.name)}"
  let cbs : Array Cb := #[⟨"inc", (· + 1)⟩, ⟨"dbl", (· * 2)⟩, ⟨"sq", fun x => x * x⟩]
  let cbs := (cbs.set! 1 ⟨"neg", fun x => 100 - x⟩).pop
  IO.println s!"cbs {cbs.map (·.name)} {cbs.map (·.f 7)}"
  let jobs : Array Job := (Array.range 4).map fun i => ⟨i, Task.spawn fun _ => i * i⟩
  let jobs := (jobs.set! 0 ⟨9, .pure 81⟩).pop
  IO.println s!"jobs {jobs.map (·.id)} {jobs.map (·.t.get)}"
  let strs : Array String := (Array.range 5).map toString
  IO.println s!"strs {strs.set! 0 "zero"} {strs.pop}"
  -- drop the array that holds handles, then read the files
  rs := #[]
  IO.println s!"after {rs.size}"
  ha.flush; hb.flush; hc.flush
  IO.println (← readAll names)
  for n in names do IO.FS.removeFile n
