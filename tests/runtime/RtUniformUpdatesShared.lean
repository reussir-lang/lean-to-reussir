/-! Runtime test: a uniform column (`data : Array ty.denote`, mono
`Array lcAny`) passed at every step to a helper taking `Array Nat` that is
also called with a typed array elsewhere (review of uniform-updates round 3,
rv9/containers/c02review/round3 C03R-01). `uniformParams` makes a parameter
uniform only when every call site passes a uniform array, so this helper
keeps `Array Nat`, and the column is converted to it at each call: linear
work per step, quadratic in the loop, where natively the call is O(1)
(20000 steps: 0.79 s, 0.00 s natively). A known difference (plan §10,
"Structural conversions"; a copy of the helper with the parameter uniform
for the uniform call sites would remove it). The output is checked here,
not the time. -/
inductive Ty | nat | str

@[reducible] def Ty.denote : Ty → Type
  | .nat => Nat
  | .str => String

structure Column where
  ty : Ty
  data : Array ty.denote

-- A utility used by typed code and by the column.
@[noinline] def firstPlusSize (a : Array Nat) : Nat := a.size + a[0]!

def Column.step (c : Column) (i : Nat) : Column × Nat :=
  match c with
  | ⟨.nat, d⟩ =>
    let d' := d.push i
    (⟨.nat, d'⟩, firstPlusSize d')
  | c => (c, 0)

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 300
  let typed : Array Nat := #[4, 5, 6]
  let mut acc := firstPlusSize typed
  let mut c : Column := ⟨.nat, #[1]⟩
  for i in [0:n] do
    let (c', x) := c.step i
    c := c'
    acc := acc + x
  match c with
  | ⟨.nat, d⟩ => IO.println s!"{d.size} {acc}"
  | ⟨.str, d⟩ => IO.println s!"{d.size}"
