/-! Runtime test: updated columns (`data : Array ty.denote`, mono
`Array lcAny`) through nested join points, with the updated column used
afterwards in different ways: uniform updates only (and captured by a
`dbgTrace` closure on a rare path), a read at the precise type (`foldl` at
`Nat`, every 997 steps), captured in a closure (review of RV9C-02's fix,
rv9/containers/c02review/round2, C2Jp). `uniform-updates` keeps each chain
uniform: a join point's parameter planned in one round can be the jump
argument that lets another join point's parameter be planned, so the
candidates are made until none is added (a first version depended on the
order in which it looked at the join points: the `foldl` column stayed
`Array Nat` and was converted at every step). Output checked here;
tests/runtime/conv-count-check.sh runs it at two sizes. -/
inductive Ty | nat | str
  deriving BEq

@[reducible] def Ty.denote : Ty → Type
  | .nat => Nat
  | .str => String

structure Column where
  ty : Ty
  data : Array ty.denote

-- Uniform uses only (size, push, the constructor).
def Column.a (c : Column) (i : Nat) : Column :=
  match c with
  | ⟨.nat, d⟩ =>
    let d' := if i % 2 == 0 then d.push i else d.set! 0 i
    let d'' := if d'.size % 3 == 0 then d'.push 1 else d'
    if d''.size % 1000 == 999 then dbgTrace s!"a {d''.size}" fun _ => ⟨.nat, d''⟩ else ⟨.nat, d''⟩
  | c => c

-- A read at the precise type after the join (foldl at Nat).
def Column.b (c : Column) (i : Nat) : Column × Nat :=
  match c with
  | ⟨.nat, d⟩ =>
    let d' := if i % 2 == 0 then d.push i else d.set! 0 i
    let s := if i % 997 == 0 then d'.foldl (· + ·) 0 else d'.size
    (⟨.nat, d'⟩, s)
  | c => (c, 0)

-- Captured in a closure.
def Column.c (c : Column) (i : Nat) : Column × (Unit → Nat) :=
  match c with
  | ⟨.nat, d⟩ =>
    let d' := if i % 2 == 0 then d.push i else d.set! 0 i
    (⟨.nat, d'⟩, fun _ => d'.size + d'[0]!)
  | c => (c, fun _ => 0)

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 1000
  let mut a : Column := ⟨.nat, #[0]⟩
  let mut b : Column := ⟨.nat, #[0]⟩
  let mut c : Column := ⟨.nat, #[0]⟩
  let mut acc := 0
  let mut f : Unit → Nat := fun _ => 0
  for i in [0:n] do
    a := a.a i
    let (b', s) := b.b i
    b := b'
    acc := acc + s
    let (c', g) := c.c i
    c := c'
    f := g
  let size (x : Column) : Nat := match x with | ⟨.nat, d⟩ => d.size + d.foldl (· + ·) 0 | ⟨.str, d⟩ => d.size
  IO.println s!"{size a} {size b} {acc} {size c} {f ()}"
