/-! Runtime test: a growing typed list packed into an existential at every
step of a loop (blowup audit BA-09). `Packed` hides the element type (`α`
is a field), so `Packed.headVal` is uniform code over a `List lcAny`
(elements in `L2RBox`). Packing the typed `List Nat` converts the whole
list, so step i costs O(i) and the loop O(n^2) (32012000 cells at
n = 8000; natively a packing is O(1)). The output is checked here; the
allocations by tests/runtime/alloc-check.sh (RtReprExistRepack.alloc). -/
structure Packed where
  α : Type
  xs : List α
  f : α → Nat

@[noinline] def Packed.headVal (p : Packed) : Nat :=
  match p.xs with
  | [] => 0
  | x :: _ => p.f x

def main (args : List String) : IO Unit := do
  let n := (args.headD "300").toNat!
  let mut xs : List Nat := []
  let mut acc := 0
  for i in [0:n] do
    xs := i :: xs
    acc := acc + Packed.headVal ⟨Nat, xs, id⟩
  IO.println s!"{acc} {xs.length}"
