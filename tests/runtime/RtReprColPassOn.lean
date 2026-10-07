/-! Runtime test: a uniform column (`data : Array ty.denote`) whose `.nat`
branch calls `stats`, which takes an `Array Nat` and only passes it on to
another function at the precise type (`sumFirst`) (blowup audit BA-13).
`uniform-updates` makes a parameter uniform only when its body uses it
uniformly (`uniformParams`); passing it on at `Array Nat` is not uniform,
so the column is converted to `Array Nat` at each call: O(n) per step,
O(n^2) in the loop (32012001 elements for 8000 steps; natively O(1) per
step). Like C03R-01 (RtUniformUpdatesShared), with the typed use one call
deeper. The output is checked here; the allocations by
tests/runtime/alloc-check.sh (RtReprColPassOn.alloc). -/
inductive Ty | nat | str

@[reducible] def Ty.denote : Ty → Type
  | .nat => Nat
  | .str => String

structure Column where
  ty : Ty
  data : Array ty.denote

@[noinline] def sumFirst (a : Array Nat) : Nat := a[0]! + a.size

@[noinline] def stats (a : Array Nat) (k : Nat) : Nat := sumFirst a + k

def Column.step (c : Column) (i : Nat) : Column × Nat :=
  match c with
  | ⟨.nat, d⟩ =>
    let d' := d.push i
    (⟨.nat, d'⟩, stats d' i)
  | c => (c, 0)

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 300
  let mut acc := 0
  let mut c : Column := ⟨.nat, #[1]⟩
  for i in [0:n] do
    let (c', x) := c.step i
    c := c'
    acc := acc + x
  match c with
  | ⟨.nat, d⟩ => IO.println s!"{d.size} {acc}"
  | ⟨.str, d⟩ => IO.println s!"{d.size}"
