/-! Runtime test: a self tail-recursive loop that swaps its two list
parameters, where one list also goes into an existential (uniform code)
and the other stays typed (design review of the layout redesign,
correctness, DRC-07). A translation that made one copy of `go` per
layout of its arguments would give `go` at (uniform, typed) and at
(typed, uniform), calling each other in tail position: Reussir guarantees
no tail call between two functions, so that would take a stack frame per
iteration. Native Lean runs the loop in constant stack. The argument
(`RtReprSwapLoop.args`, 10^8 iterations) is large enough that a stack
frame per iteration, even 16 bytes, overflows the 1 GiB stack `main` runs
on. Native result at n = 10^6: 2500003. -/
structure Pk where
  α : Type
  xs : List α
  f : List α → Nat

@[noinline] def useP (p : Pk) : Nat := p.f p.xs

@[noinline] def go : Nat → List Nat → List Nat → Nat → Nat
  | 0, a, _, acc => acc + a.length
  | n + 1, a, b, acc => go n b a (acc + (a.headD 0))

def main (args : List String) : IO Unit := do
  let n := (args.headD "1000000").toNat!
  let u : List Nat := [1, 2, 3]
  let t : List Nat := [4, 5]
  let s := useP ⟨Nat, u, List.length⟩   -- u goes into the existential
  IO.println s!"{s} {go n u t 0}"
