/-! Runtime test: a dependent payload read again and again, the two shapes
of blowup audit BA-17 that the tests of a `match` on a `Box` (RtBoxMatchReads,
RtBoxMatchFallback) do not take. Mode `copyR`: one payload in a structure
whose field type is a reducible family (`ty.listDenoteR`), copied k times
through a function and read by an O(1) match each time. Mode `rebox`: a
typed list boxed again at every step (a new structure from `i :: xs`, the
non-reducible family) and read by an O(1) match. Native Lean copies no
list in either mode (a read is O(1)); a read that converts the whole
payload to the uniform layout costs O(n) per read (copyR: 8004056
allocations for 1000 reads of a list of 4000, natively 15083). The output
is checked here; the allocations by tests/runtime/alloc-check.sh
(RtReprBoxCopy.alloc). Arguments: MODE K N (default: both modes, 50 50). -/
inductive Ty | nat | str

-- `ty.listDenote` is not reducible: the payload is one boxed value.
def Ty.listDenote : Ty → Type
  | .nat => List Nat
  | .str => List String

structure DL where
  ty : Ty
  v : ty.listDenote

-- The same with a reducible family.
@[reducible] def Ty.listDenoteR : Ty → Type
  | .nat => List Nat
  | .str => List String

structure DLR where
  ty : Ty
  v : ty.listDenoteR

@[noinline] def copyDLR (d : DLR) : DLR := ⟨d.ty, d.v⟩
@[noinline] def headDLR (d : DLR) : Nat :=
  match d with
  | ⟨.nat, x :: _⟩ => x + 1
  | _ => 0
@[noinline] def headDL (d : DL) : Nat :=
  match d with
  | ⟨.nat, (x :: _ : List Nat)⟩ => x + 1
  | _ => 0

def run (mode : String) (k n : Nat) : Nat := Id.run do
  let xs : List Nat := List.range n
  let mut acc := 0
  if mode == "copyR" then
    let mut d : DLR := ⟨.nat, xs⟩
    for _ in [0:k] do
      d := copyDLR d
      acc := acc + headDLR d
  else if mode == "rebox" then
    for i in [0:k] do
      acc := acc + headDL ⟨.nat, (i :: xs : List Nat)⟩ - i
  return acc

def main (args : List String) : IO Unit := do
  let k := (args.getD 1 "50").toNat!
  let n := (args.getD 2 "50").toNat!
  let modes := match args.head? with
    | some m => [m]
    | none => ["copyR", "rebox"]
  for m in modes do
    IO.println s!"{m} {run m k n}"
