/-! Runtime test: a column of lists (`data : List ty.denote`, mono
`List lcAny`) whose `.nat` branch conses a number and then reads the head
with a library function at the precise type (`List.head!` at `Nat`)
(blowup audit BA-11). `uniform-updates` builds a cons on the uniform list
only when every use of the result expects the uniform type
(Opt/UniformUpdates.lean, the constructor rule); the typed `head!` blocks
it, so each step converts the column to `List Nat`, conses, and converts it
back: O(n) per step, O(n^2) in the loop (64024002 cells for 8000 steps;
natively O(1) per step). The output is checked here; the allocations by
tests/runtime/alloc-check.sh (RtReprColListLib.alloc). -/
inductive Ty | nat | str

@[reducible] def Ty.denote : Ty → Type
  | .nat => Nat
  | .str => String

structure Column where
  ty : Ty
  data : List ty.denote

def Column.step (c : Column) (i : Nat) : Column × Nat :=
  match c with
  | ⟨.nat, d⟩ =>
    let d' := i :: d
    (⟨.nat, d'⟩, d'.head! + 1)
  | c => (c, 0)

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 300
  let mut acc := 0
  let mut c : Column := ⟨.nat, []⟩
  for i in [0:n] do
    let (c', x) := c.step i
    c := c'
    acc := acc + x
  match c with
  | ⟨.nat, d⟩ => IO.println s!"{d.length} {acc}"
  | ⟨.str, d⟩ => IO.println s!"{d.length}"
