/-! Runtime test: updates of a column whose element type depends on a value
(`data : Array ty.denote`, mono `Array lcAny`) whose result goes through a
join point that Lean types at the precise array type (review of RV9C-02's
fix, rv9/containers/c02review C02R-01). Here the join point is the
`(⟨.nat, _⟩, 0)` that several match arms share: one arm runs
`Array.modify` (whose bounds check also jumps with the array), one an
update under an `if`. `uniform-updates` kept an update's result uniform only
when every use expected `Array lcAny`, and a jump to a join point whose
parameter is `Array Nat` is not such a use: the whole column was converted
to `Array Nat` and back at every step (20000 steps: 3.9 s for 0.00 s
natively). A join point's parameter is now part of the pass's fixpoint: it
becomes `Array lcAny` when every jump passes a uniform value and every use
expects one. Output checked here; tests/runtime/conv-count-check.sh runs
this program at two sizes and counts the elements conversions rebuild. -/
inductive Ty | nat | str

@[reducible] def Ty.denote : Ty → Type
  | .nat => Nat
  | .str => String

structure Column where
  ty : Ty
  data : Array ty.denote

def Column.step (c : Column) (k : Nat) (i : Nat) : Column × Nat :=
  match c, k with
  | ⟨.nat, d⟩, 0 => (⟨.nat, d.modify (i % d.size) (· + 1)⟩, 0)
  | ⟨.nat, d⟩, 1 => (⟨.nat, d⟩, d.back! + d[i % d.size]!)
  | ⟨.nat, d⟩, 2 => (⟨.nat, if i % 2 == 0 then (d.pop).push i else d.set! 0 i⟩, 0)
  | ⟨.nat, d⟩, _ => (⟨.nat, if i % 7 == 100 then d else d.set! 0 i⟩, 0)
  | c, _ => (c, 0)

def run (n k : Nat) : String := Id.run do
  let mut c : Column := ⟨.nat, (Array.range n : Array Nat)⟩
  let mut acc := 0
  for i in [0:n] do
    let (c', a) := c.step k i
    c := c'
    acc := acc + a
  match c with
  | ⟨.nat, d⟩ => s!"{k}: {d.size} {d.foldl (· + ·) 0} {acc}"
  | ⟨.str, d⟩ => s!"{k}: {d.size}"

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 300
  for k in [0, 1, 2, 3] do
    IO.println (run n k)
