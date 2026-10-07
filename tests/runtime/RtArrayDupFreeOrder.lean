/-! Runtime test (review of the runtime's speed items, finding F1): the
order of the releases of an array's elements when an element is shared
inside the array: the same box twice, or a value that is also held by a
later element. Natively `lean_del` first decrements every element in index
order, pushing each one whose count reaches zero, then frees the pushed ones
last first; so a value shared inside the array is freed at its last
occurrence (`dup`), and a value that a later element also holds is freed
inside that element's release (`holder`). Each handle's buffered tag reaches
the file when the handle is closed. The array is freed outside a free (a
reference set gives it up) and inside one (it is a field of a structure
that a reference set gives up). Native output: `dup dbca` and `holder acb`,
outside a free and inside one. leanrt freed an array from its last element
while decrementing (`dcba`, `cba`); it now makes native's two passes
(`drop::free_vec`, `ReleaseElems::scan`). -/

def path : System.FilePath := "adf-tmp.txt"

@[noinline] def openW (tag : String) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk path .append
  h.putStr tag
  pure h

@[noinline] def report (name : String) : IO Unit := do
  IO.println s!"{name} {← IO.FS.readFile path}"
  IO.FS.writeFile path ""

/-- `some b` at indices 1 and 4, held only by the array: natively `dbca`. -/
@[noinline] def buildDup : IO (Array (Option IO.FS.Handle)) := do
  let a ← openW "a"; let b ← openW "b"; let c ← openW "c"; let d ← openW "d"
  let sb := some b
  pure #[some a, sb, none, some c, sb, some d]

/-- `x` at index 0 and as the tail of `y` at index 2: natively `acb`. -/
@[noinline] def buildHolder : IO (Array (List IO.FS.Handle)) := do
  let a ← openW "a"; let b ← openW "b"; let c ← openW "c"
  let x := [a]
  pure #[x, [b], c :: x]

structure Box (α : Type) where
  n : Nat
  xs : Array α

def main : IO Unit := do
  IO.FS.writeFile path ""
  let r ← IO.mkRef (#[] : Array (Option IO.FS.Handle))
  r.set (← buildDup)
  IO.println s!"dup size {(← r.get).size}"
  r.set #[]
  report "dup"
  let r2 ← IO.mkRef (#[] : Array (List IO.FS.Handle))
  r2.set (← buildHolder)
  IO.println s!"holder size {(← r2.get).size}"
  r2.set #[]
  report "holder"
  let r3 ← IO.mkRef (some (Box.mk 0 (#[] : Array (Option IO.FS.Handle))))
  r3.set (some ⟨1, ← buildDup⟩)
  IO.println s!"dup in free {(← r3.get).map (·.xs.size)}"
  r3.set none
  report "dup in free"
  let r4 ← IO.mkRef (some (Box.mk 0 (#[] : Array (List IO.FS.Handle))))
  r4.set (some ⟨1, ← buildHolder⟩)
  IO.println s!"holder in free {(← r4.get).map (·.xs.size)}"
  r4.set none
  report "holder in free"
  IO.FS.removeFile path
