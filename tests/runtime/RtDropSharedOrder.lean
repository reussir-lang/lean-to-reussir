/-! The trailing elements of an array that are shared (count > 1) are
decremented when the array's count reaches 0 (`free_vec`), even inside an
active drain, where the array itself is only pushed: a later field of the
record being freed that holds the same element then frees it first. -/
structure W where
  h : IO.FS.Handle
  tag : String

structure R where
  xs : Array W
  z : W
  y : W

def hnd (path : System.FilePath) (tag : String) : IO W := do
  let h ← IO.FS.Handle.mk path .append
  h.putStr s!"{tag} "
  return ⟨h, tag⟩

@[noinline] def dropRs (xs : Array R) : Nat := xs.size
@[noinline] def dropR (r : R) : Nat := r.xs.size

def main : IO Unit := do
  let p : System.FilePath := "dropshared.txt"
  -- 1: shared element last in the array
  IO.FS.writeFile p ""
  let y ← hnd p "y1"
  let z ← hnd p "z1"
  IO.println s!"case1 {dropRs #[⟨#[y], z, y⟩]}"
  IO.println (← IO.FS.readFile p)
  -- 2: unique element before the shared one
  IO.FS.writeFile p ""
  let y ← hnd p "y2"
  let z ← hnd p "z2"
  let u ← hnd p "u2"
  IO.println s!"case2 {dropRs #[⟨#[u, y], z, y⟩]}"
  IO.println (← IO.FS.readFile p)
  -- 3: unique element last (no pre-decrement): matches
  IO.FS.writeFile p ""
  let y ← hnd p "y3"
  let z ← hnd p "z3"
  let u ← hnd p "u3"
  IO.println s!"case3 {dropRs #[⟨#[y, u], z, y⟩]}"
  IO.println (← IO.FS.readFile p)
  -- 4: the record dropped by itself (no drain active): matches
  IO.FS.writeFile p ""
  let y ← hnd p "y4"
  let z ← hnd p "z4"
  IO.println s!"case4 {dropR ⟨#[y], z, y⟩}"
  IO.println (← IO.FS.readFile p)
  IO.FS.removeFile p
