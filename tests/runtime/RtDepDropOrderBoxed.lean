/-! Runtime test: the order in which file handles held in boxes (the
elements of a `List IO.FS.Handle`, the fields of a structure over a type
parameter: every such position is a box, rule 1), and for comparison in a
record of a monomorphic type, are closed when user code drops the value by
itself, with no container around it (adversarial review of the
dependent-type branch, finding 3). Each handle's buffered tag
reaches the shared file when the handle is closed. A documented difference
(plan §10, "Order of releases in one free"): `RtDepDropOrderBoxed.l2r.out`
is lean2rr's output, `RtDepDropOrderBoxed.native.out` native's.

- `nest`: `{inner := ⟨a, b⟩, arr := #[c, d], opt := some e}` built by
  another function and dropped by `main` after a call that borrows it.
  Natively `lean_dec` frees it last field first: `edcba`. lean2rr: `abdce`.
  Reussir's release of the first cell goes through its fields in field
  order; a box whose last reference it drops is released at once (inner's
  `a`, `b`, then opt's `e`), and the array frees its elements last first
  (`dc`).
- `list`: `[h1, …, h8]` built in `main` and dropped after `hs.length`.
  Natively Lean knows the constructor there (`lean_dec_ref_known`): the
  first cell's fields in order, each completely, then the rest last first:
  `18765432`. lean2rr: `12876543`. Reussir's release of the first cell
  also releases the members of the second cell before it drains the stack
  of pending work, so the boxes of the first two cells are released at
  once; from the third cell on they are pushed and released last first.
- `built`: the same list made by another function and dropped by `main`.
  Natively `lean_dec`, all last first: `87654321`. lean2rr: `12876543`.
- `pair`: a list holding one structure `{a := #[A0, A1], l := [L0, L1]}`,
  dropped after `length`: `L1L0A1A0`, as natively. The structure is the
  payload of a box, released inside a free of the runtime: its fields go
  on the stack of pending work and come back last first.
- `typed`: the same structure in a monomorphic list type (`ALs`, whose
  field is the record itself, no box): natively `L1L0A1A0`, lean2rr
  `A1A0L1L0`. Reussir's release of the first cell releases the record's
  fields while no free runs, and the array frees its elements as soon as
  the release reaches it.

Before the one-word box (dev, with the enum `L2RBox`), a boxed handle was a
record cell, which Reussir's release pushes from the second cell on:
`badce`, `18765432` for both lists (natively so in the `list` case), and
`A1A0L1L0` (the structure's release, outside a free, freed the array as
soon as it reached it). -/

structure Two (α : Type) where
  a : α
  b : α

structure Nest (α : Type) where
  inner : Two α
  arr : Array α
  opt : Option α

/-- An array and a list of handles in one structure. -/
structure AL where
  a : Array IO.FS.Handle
  l : List IO.FS.Handle

/-- A monomorphic list of `AL`: its field is the record itself, no box. -/
inductive ALs where
  | cons (p : AL) (t : ALs)
  | nil

@[noinline] def ALs.len : ALs → Nat
  | .cons _ t => t.len + 1
  | .nil => 0

def path : System.FilePath := "dob-tmp.txt"

@[noinline] def openW (tag : String) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk path .append
  h.putStr tag
  pure h

@[noinline] def build : IO (Nest IO.FS.Handle) := do
  let a ← openW "a"
  let b ← openW "b"
  let c ← openW "c"
  let d ← openW "d"
  let e ← openW "e"
  pure { inner := ⟨a, b⟩, arr := #[c, d], opt := some e }

@[noinline] def consume {α : Type} (n : Nest α) : Nat := n.arr.size

@[noinline] def buildList : IO (List IO.FS.Handle) := do
  let mut hs := []
  for i in [0:8] do
    hs := (← openW s!"{8 - i}") :: hs
  pure hs

def report (tag : String) : IO Unit := do
  IO.println s!"{tag} {← IO.FS.readFile path}"
  IO.FS.writeFile path ""

def main : IO Unit := do
  IO.FS.writeFile path ""
  let n ← build
  IO.println s!"nest size {consume n}"
  report "nest"
  let hs : List IO.FS.Handle :=
    [← openW "1", ← openW "2", ← openW "3", ← openW "4",
     ← openW "5", ← openW "6", ← openW "7", ← openW "8"]
  IO.println s!"list length {hs.length}"
  report "list"
  let hs ← buildList
  IO.println s!"built length {hs.length}"
  report "built"
  let al : List AL := [⟨#[← openW "A0", ← openW "A1"], [← openW "L0", ← openW "L1"]⟩]
  IO.println s!"pair length {al.length}"
  report "pair"
  let als : ALs := .cons ⟨#[← openW "A0", ← openW "A1"], [← openW "L0", ← openW "L1"]⟩ .nil
  IO.println s!"typed length {als.len}"
  report "typed"
  IO.FS.removeFile path
