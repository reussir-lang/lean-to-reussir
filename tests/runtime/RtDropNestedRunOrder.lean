/-! Runtime test (port to upstream Reussir's drop scopes, 2026-11-18): the
order of the closes when a free of the runtime (an array's, a thunk's, a
reference's `set`) releases a box whose payload is a record with a tree
in it and a handle after the tree. `Tr` has two recursive fields, so
Reussir frees it through its worklist. Native Lean frees through one
stack, last pushed first: a record's last field first.

With a payload release that drops the record in place, upstream Reussir
(36a55a0f) freed the tree as a drop run of its own, which is complete
before the record's next field is reached: `T` before `H`, natively `H`
before `T`. The payload's release goes through the record's FFI release
(Lower/Finish, `payloadJoins`), which joins the running free.

Each handle's buffered tag reaches the shared file when the handle is
closed, so the file shows the order.

- `struct`: `{t := node leaf T leaf, h := H}` in an array: `HT`.
- `two`: two such structures in an array, the last element first:
  `KUHT`.
- `trees`: a list type of the program with a tree in each cell
  (`cons t rest`), in an array: the rest of the list before the cell's
  tree: `21`.
- `thunk`: the structure as the value of a thunk: `HT`.
- `ref`: the structure in a reference, replaced by `set`: `HT`.
- `inner`: a structure whose first field is such a structure: `GHT`. -/
inductive Tr where
  | leaf : Tr
  | node : Tr → IO.FS.Handle → Tr → Tr

structure S where
  t : Tr
  h : IO.FS.Handle

structure O where
  s : S
  g : IO.FS.Handle

inductive TL where
  | nil : TL
  | cons (t : Tr) (rest : TL) : TL

def path : System.FilePath := "dnr-tmp.txt"

@[noinline] def openW (tag : String) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk path .append
  h.putStr tag
  pure h

def report (tag : String) : IO Unit := do
  IO.println s!"{tag} {← IO.FS.readFile path}"
  IO.FS.writeFile path ""

@[noinline] def mkS (t h : String) : IO S := do
  let th ← openW t
  let hh ← openW h
  pure { t := .node .leaf th .leaf, h := hh }

@[noinline] def dropArr {α} (xs : Array α) : Nat := xs.size
@[noinline] def dropThunk {α} (_t : Thunk α) : Nat := 7

def main : IO Unit := do
  IO.FS.writeFile path ""
  IO.println s!"size {dropArr #[← mkS "T" "H"]}"
  report "struct"
  IO.println s!"size {dropArr #[← mkS "T" "H", ← mkS "U" "K"]}"
  report "two"
  let t1 ← openW "1"
  let t2 ← openW "2"
  IO.println s!"size {dropArr #[TL.cons (.node .leaf t1 .leaf) (.cons (.node .leaf t2 .leaf) .nil)]}"
  report "trees"
  let s ← mkS "T" "H"
  IO.println s!"thunk {dropThunk (Thunk.pure s)}"
  report "thunk"
  let r ← IO.mkRef (some (← mkS "T" "H"))
  r.set none
  report "ref"
  let s ← mkS "T" "H"
  let g ← openW "G"
  IO.println s!"size {dropArr #[({ s, g } : O)]}"
  report "inner"
  IO.FS.removeFile path
