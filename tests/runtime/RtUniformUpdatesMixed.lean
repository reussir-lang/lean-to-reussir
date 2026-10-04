/-! Runtime test: updates of a uniform column (`data : Array ty.denote`,
mono `Array lcAny`) whose result also has one use at the precise type
(review of RV9C-02's fix, rv9/containers/c02review/round2 C02R-02). Such a
use kept the update's result, and the join point it goes through, at
`Array Nat`, so the whole column was converted there and back at every step
(quadratic), even when that use is rare:
- `mixed`: one side of the `if` is a fresh `Array Nat` (a reset that never
  happens here); the join point stayed precise.
- `rareRead`: a `foldl` at `Nat` every 997 steps.
- `captured`: the updated column captured by a closure.
At 20000 steps: 4.2 s vs 0.09 s natively. `uniform-updates` now keeps the
chain uniform, converts a precise read at that read, a fresh array at its
jump, and makes the parameter of the closure (and of the fold loop) uniform,
since every caller passes it a uniform array. Output checked here;
tests/runtime/conv-count-check.sh runs this program at two sizes and counts
the elements conversions rebuild. -/
inductive Ty | nat | str

@[reducible] def Ty.denote : Ty → Type
  | .nat => Nat
  | .str => String

structure Column where
  ty : Ty
  data : Array ty.denote

def Column.mixed (c : Column) (i : Nat) : Column :=
  match c with
  | ⟨.nat, d⟩ =>
    let d' := if i % 100000 == 99999 then #[i] else d.push i
    let s := d'.size
    if s % 1000 == 999 then ⟨.nat, d'.push 0⟩ else ⟨.nat, d'⟩
  | c => c

def Column.rareRead (c : Column) (i : Nat) : Column × Nat :=
  match c with
  | ⟨.nat, d⟩ =>
    let d' := if i % 2 == 0 then d.push i else d.set! 0 i
    let s := if i % 997 == 0 then d'.foldl (· + ·) 0 else d'.size
    (⟨.nat, d'⟩, s)
  | c => (c, 0)

def Column.captured (c : Column) (i : Nat) : Column × (Unit → Nat) :=
  match c with
  | ⟨.nat, d⟩ =>
    let d' := if i % 2 == 0 then d.push i else d.set! 0 i
    (⟨.nat, d'⟩, fun _ => d'.size + d'[0]!)
  | c => (c, fun _ => 0)

def total (x : Column) : Nat :=
  match x with
  | ⟨.nat, d⟩ => d.size + d.foldl (· + ·) 0
  | ⟨.str, d⟩ => d.size

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 300
  let mut a : Column := ⟨.nat, #[0]⟩
  let mut b : Column := ⟨.nat, #[0]⟩
  let mut c : Column := ⟨.nat, #[0]⟩
  let mut acc := 0
  let mut f : Unit → Nat := fun _ => 0
  for i in [0:n] do
    a := a.mixed i
    let (b', s) := b.rareRead i
    b := b'
    acc := acc + s
    let (c', g) := c.captured i
    c := c'
    f := g
  IO.println s!"{total a} {total b} {acc} {total c} {f ()}"
