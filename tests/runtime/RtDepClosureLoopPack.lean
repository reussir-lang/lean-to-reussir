/-! Runtime test: a growing list packed into an existential at every step
(blowup audit BA-09), where the loop is a closure applied by a function
that Lean does not specialize (a function value stored in a structure),
and the packing is in a helper the closure calls (design review of the
layout redesign, performance, repro ClosureLoopPack). Native Lean packs in
O(1). A translation that converts the list when it packs it is quadratic.
The output is checked here; the allocations by tests/runtime/alloc-check.sh
(RtDepClosureLoopPack.alloc). Argument: N (default 1000). -/
structure Packed where
  α : Type
  xs : List α
  f : α → Nat

@[noinline] def Packed.headVal (p : Packed) : Nat :=
  match p.xs with
  | [] => 0
  | x :: _ => p.f x

/-- The helper: packs the (typed) list. -/
@[noinline] def packStep (xs : List Nat) : Nat := Packed.headVal ⟨Nat, xs, id⟩

/-- A driver holding the step as data (not specialized by Lean). -/
structure Driver where
  step : Nat × List Nat → Nat → Nat × List Nat

@[noinline] def Driver.run (d : Driver) : Nat → Nat × List Nat → Nat × List Nat
  | 0, s => s
  | n + 1, s => d.run n (d.step s n)

def main (args : List String) : IO Unit := do
  let n := (args.headD "1000").toNat!
  let d : Driver := ⟨fun (acc, xs) i => let xs := i :: xs; (acc + packStep xs, xs)⟩
  let (acc, xs) := d.run n (0, [])
  IO.println s!"{acc} {xs.length}"
