/-! Runtime test: a typed helper probed with a uniform column at every step
(blowup audit, probe ColUpdateTyped, checked and not a problem). The
column's `data : Array ty.denote` is uniform; its `.nat` branch passes it
to `probeArr`, which takes an `Array Nat` and only reads it, and every
call site of `probeArr` passes a uniform array, so `uniform-updates` makes
its parameter uniform (`uniformParams`): no conversion per call, the
bytes allocated grow with n as native's do. (C03R-01, RtUniformUpdatesShared,
is the same with one more, typed, call site.) The output is checked here;
the allocations by tests/runtime/alloc-check.sh
(RtReprColUpdateTyped.alloc). -/
inductive Ty | nat | str

@[reducible] def Ty.denote : Ty → Type
  | .nat => Nat
  | .str => String

structure Column where
  ty : Ty
  data : Array ty.denote

@[noinline] def probeArr (a : Array Nat) (i : Nat) : Nat := a[i % a.size]! + a.size

def Column.probe (c : Column) (i : Nat) : Nat :=
  match c with
  | ⟨.nat, d⟩ => probeArr d i
  | _ => 0

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 300
  let c : Column := ⟨.nat, Array.range n⟩
  let mut acc := 0
  for i in [0:n] do
    acc := acc + c.probe i
  IO.println acc
