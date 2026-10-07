/-! Runtime test: the order in which file handles held in records (lists,
trees, structures) are closed when an array holding the records is dropped
at once (each handle's tag reaches the shared file when it is closed).
Native Lean frees through one stack of objects, last pushed first: a
record's fields are pushed in order, so its last field is freed first, and
a freed object's children before the objects pushed earlier. Here the
array's free (`leanrt::drop`) and Reussir's drop glue for the records
(local patch 13-b) share one stack of pending work, so the order is the
same (plan §10). -/
inductive Tr where
  | leaf : Tr
  | node : Tr → IO.FS.Handle → Tr → Tr

structure Two where
  a : IO.FS.Handle
  b : IO.FS.Handle

structure Mix where
  l : List IO.FS.Handle
  t : Tr
  a : Array IO.FS.Handle
  h : IO.FS.Handle

def hnd (path : System.FilePath) (tag : String) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk path .append
  h.putStr s!"{tag} "
  return h

def mkList (path : System.FilePath) (p : String) : Nat → List IO.FS.Handle → IO (List IO.FS.Handle)
  | 0, acc => pure acc
  | n+1, acc => do mkList path p n ((← hnd path s!"{p}{n}") :: acc)

def mkTree (path : System.FilePath) (p : String) : Nat → Nat → IO Tr
  | 0, _ => pure .leaf
  | d+1, k => do
    let l ← mkTree path p d (2 * k)
    let h ← hnd path s!"{p}{k}"
    let r ← mkTree path p d (2 * k + 1)
    pure (.node l h r)

@[noinline] def dropLists (xs : Array (List IO.FS.Handle)) : Nat := xs.size
@[noinline] def dropTrees (xs : Array Tr) : Nat := xs.size
@[noinline] def dropTwos (xs : Array Two) : Nat := xs.size
@[noinline] def dropMixes (xs : Array Mix) : Nat := xs.size
@[noinline] def dropNested (xs : Array (Array (List IO.FS.Handle))) : Nat := xs.size

def main : IO Unit := do
  let p : System.FilePath := "droporderrec.txt"
  IO.FS.writeFile p ""
  let l1 ← mkList p "A" 4 []
  let l2 ← mkList p "B" 3 []
  IO.println s!"lists {dropLists #[l1, l2]}"
  IO.println (← IO.FS.readFile p)
  IO.FS.writeFile p ""
  let t1 ← mkTree p "T" 3 1
  let t2 ← mkTree p "U" 2 1
  IO.println s!"trees {dropTrees #[t1, t2]}"
  IO.println (← IO.FS.readFile p)
  IO.FS.writeFile p ""
  let a1 ← hnd p "a1"
  let b1 ← hnd p "b1"
  let a2 ← hnd p "a2"
  let b2 ← hnd p "b2"
  IO.println s!"twos {dropTwos #[⟨a1, b1⟩, ⟨a2, b2⟩]}"
  IO.println (← IO.FS.readFile p)
  IO.FS.writeFile p ""
  let ml ← mkList p "L" 3 []
  let mt ← mkTree p "T" 2 1
  let ma1 ← hnd p "a1"
  let ma2 ← hnd p "a2"
  let mh ← hnd p "h"
  let nl ← mkList p "M" 2 []
  let nh ← hnd p "g"
  IO.println s!"mixes {dropMixes #[⟨ml, mt, #[ma1, ma2], mh⟩, ⟨nl, .leaf, #[], nh⟩]}"
  IO.println (← IO.FS.readFile p)
  IO.FS.writeFile p ""
  let x1 ← mkList p "X" 2 []
  let x2 ← mkList p "Y" 2 []
  let x3 ← mkList p "Z" 3 []
  IO.println s!"nested {dropNested #[#[x1, x2], #[x3]]}"
  IO.println (← IO.FS.readFile p)
  IO.FS.removeFile p
