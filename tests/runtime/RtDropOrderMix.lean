/-! Runtime test (review of the shared drop stack, its leanrt side): the
order of handle closes where leanrt containers (arrays, thunks, tasks,
references) and Reussir records (trees, structures, closures, lists) nest
in each other, and a subtree is shared by two fields. With a drop stack of
Reussir's own beside leanrt's, the closes came out per subtree; with one
stack for both they are native's. -/
inductive Tr where
  | leaf : Tr
  | node : Tr → IO.FS.Handle → Tr → Tr

structure S where
  t : Tr
  a : Array IO.FS.Handle
  f : Unit → IO Unit
  h : IO.FS.Handle

def hnd (path : System.FilePath) (tag : String) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk path .append
  h.putStr s!"{tag} "
  return h

def mkTree (p : System.FilePath) (pre : String) : Nat → Nat → IO Tr
  | 0, _ => pure .leaf
  | d+1, k => do
    let l ← mkTree p pre d (2 * k)
    let h ← hnd p s!"{pre}{k}"
    let r ← mkTree p pre d (2 * k + 1)
    pure (.node l h r)

def mkS (p : System.FilePath) (pre : String) : IO S := do
  let t ← mkTree p s!"{pre}t" 2 1
  let a0 ← hnd p s!"{pre}a0"
  let a1 ← hnd p s!"{pre}a1"
  let c1 ← hnd p s!"{pre}c1"
  let c2 ← hnd p s!"{pre}c2"
  let h ← hnd p s!"{pre}h"
  pure { t, a := #[a0, a1], f := fun _ => do c1.putStr ""; c2.putStr "", h }

def Tr.size : Tr → Nat
  | .leaf => 0
  | .node l _ r => l.size + 1 + r.size

@[noinline] def dropArr {α} (xs : Array α) : Nat := xs.size
@[noinline] def dropList {α} (xs : List α) : Nat := xs.length
@[noinline] def dropTree (t : Tr) : Nat := t.size
@[noinline] def dropThunk {α} (_t : Thunk α) : Nat := 7
@[noinline] def dropTask {α} (_t : Task α) : Nat := 8

def dump (tag : String) (p : System.FilePath) : IO Unit := do
  IO.println s!"{tag}: {← IO.FS.readFile p}"
  IO.FS.writeFile p ""

def main : IO Unit := do
  let p : System.FilePath := "dropordermix.txt"
  IO.FS.writeFile p ""
  -- an array of structures holding a tree, an array, a closure and a handle
  let n := dropArr #[← mkS p "P", ← mkS p "Q"]
  dump s!"structs {n}" p
  -- a list of arrays of trees, in an array
  let n := dropArr #[[#[← mkTree p "A" 2 1, ← mkTree p "B" 1 1], #[← mkTree p "C" 1 1]], [#[← mkTree p "D" 1 1]]]
  dump s!"list-arrays {n}" p
  -- a thunk holding an array of trees (evaluated)
  let ts := #[← mkTree p "E" 2 1, ← mkTree p "F" 1 1]
  let n := dropThunk (Thunk.pure ts)
  dump s!"thunk {n}" p
  -- a finished task holding a tree
  let t ← mkTree p "G" 2 1
  let tk ← IO.asTask (pure t)
  let _ ← IO.wait tk
  let n := dropTask tk
  dump s!"task {n}" p
  -- a reference whose tree is replaced
  let r ← IO.mkRef (← mkTree p "H" 2 1)
  r.set .leaf
  dump "ref-set" p
  -- a subtree shared by both children, by user code and in an array
  let s ← mkTree p "S" 1 1
  let h ← hnd p "Sroot"
  let n := dropTree (.node s h s)
  dump s!"shared {n}" p
  let s ← mkTree p "U" 1 1
  let h ← hnd p "Uroot"
  let n := dropArr #[Tr.node s h s, s]
  dump s!"shared-arr {n}" p
  -- a list of trees, in an array
  let n := dropArr #[[← mkTree p "V" 2 1, ← mkTree p "W" 1 1]]
  dump s!"list-trees {n}" p
  -- a closure capturing a tree and a handle, in an array
  let t ← mkTree p "X" 2 1
  let hx ← hnd p "Xh"
  let f : Unit → IO Nat := fun _ => do hx.putStr ""; pure t.size
  let n := dropArr #[f]
  dump s!"closure {n}" p
  IO.FS.removeFile p
