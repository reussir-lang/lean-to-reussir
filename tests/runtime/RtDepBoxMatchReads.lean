/-! Runtime test: reading a dependent payload with a `match`, again and again
(blowup audit BA-17, mode copy; branch fix-box-match's RtBoxMatchReads).
`v : ty.listDenote` (a family that is not reducible) is one value of
unknown type; a match `⟨.nat, x :: _⟩` reads its head as a `Nat` and its
tail as a `List Nat`. The structure is copied through a function and read
N times. Native Lean reads in O(1): N reads of a list of N allocate
nothing per read. A translation that rebuilds the payload at each read
(every cell, every element boxed) needs N^2 cells. Cases: a list built by
typed code, a `List String`, an empty list, and lists built where the
element type is an existential's field (`Pkg`, cast to the family through
an equality). The output is checked here; the allocations by
tests/runtime/alloc-check.sh (RtDepBoxMatchReads.alloc). Argument: N
(default 50), the list's length and the number of reads. -/

inductive Ty | nat | str

def Ty.listDenote : Ty → Type
  | .nat => List Nat
  | .str => List String

structure DL where
  ty : Ty
  v : ty.listDenote

-- Through a function, so that each read is a match on a `Box`.
@[noinline] def copyDL (d : DL) : DL := ⟨d.ty, d.v⟩

@[noinline] def headDL (d : DL) : Nat :=
  match d with
  | ⟨.nat, x :: _⟩ => x + 1
  | ⟨.str, s :: _⟩ => s.length
  | _ => 0

@[noinline] def emptyDL (d : DL) : Bool :=
  match d with
  | ⟨.nat, []⟩ => true
  | _ => false

-- A list built where its element type is a field (uniform code: a list of
-- boxes), boxed as it is through an equality.
structure Pkg where
  α : Type
  xs : List α
  ty : Ty
  h : ty.listDenote = List α

@[noinline] def Pkg.toDL (p : Pkg) : DL := ⟨p.ty, p.h ▸ p.xs⟩

def reads (d : DL) (k : Nat) : Nat × Nat := Id.run do
  let mut d := d
  let mut heads := 0
  let mut empties := 0
  for _ in [0:k] do
    d := copyDL d
    heads := heads + headDL d
    if emptyDL d then empties := empties + 1
  return (heads, empties)

def main (args : List String) : IO Unit := do
  let n := (args.headD "50").toNat!
  let xs := (List.range n).map (· + 2)
  -- typed: the `Box` holds a `List Nat`
  IO.println s!"typed {reads ⟨.nat, xs⟩ n}"
  IO.println s!"typed-str {reads ⟨.str, xs.map toString⟩ n}"
  IO.println s!"empty {reads ⟨.nat, []⟩ n}"
  -- uniform: the `Box` holds a list of boxes
  IO.println s!"uniform {reads (Pkg.toDL ⟨Nat, xs, .nat, rfl⟩) n}"
  IO.println s!"uniform-empty {reads (Pkg.toDL ⟨Nat, [], .nat, rfl⟩) n}"
