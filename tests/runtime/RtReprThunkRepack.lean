/-! Runtime test: one forced thunk of a list packed into an existential at
every step of a loop (blowup audit BA-16). The package's field is
`Thunk (List α)`, in uniform code a `Thunk (List lcAny)`; converting a
forced thunk converts its value at once, so each packing copies the whole
list: O(n) per step, O(n^2) in the loop (16004000 cells at n = 4000;
natively a packing is O(1)). The thunk is still evaluated once. The output
is checked here; the allocations by tests/runtime/alloc-check.sh
(RtReprThunkRepack.alloc). -/
structure LazyList where
  α : Type
  t : Thunk (List α)
  f : α → Nat

@[noinline] def LazyList.headVal (p : LazyList) : Nat :=
  match p.t.get with
  | [] => 0
  | x :: _ => p.f x

def main (args : List String) : IO Unit := do
  let n := (args.headD "300").toNat!
  let t : Thunk (List Nat) := Thunk.mk fun _ => dbgTrace "eval" fun _ => List.range n
  let mut acc := t.get.length
  for i in [0:n] do
    acc := acc + LazyList.headVal ⟨Nat, t, (· + i)⟩
  IO.println acc
