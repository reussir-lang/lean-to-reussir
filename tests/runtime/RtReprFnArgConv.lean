/-! Runtime test: a function over lists stored in an existential next to a
list (`f : List α → Nat`), applied by uniform code to the package's list
(blowup audit BA-14). The stored function is a typed `List Nat → Nat`, so
the wrapper that lets uniform code call it converts its `List lcAny`
argument back to a `List Nat` at every application (the `.wrap` case of
`genApply`, Finish.lean): O(n) per call for a function that reads only the
head, O(n^2) for n calls (16008001 cells at n = 4000; natively O(1) per
call). The output is checked here; the allocations by
tests/runtime/alloc-check.sh (RtReprFnArgConv.alloc). -/
structure Q where
  α : Type
  xs : List α
  f : List α → Nat

@[noinline] def Q.applyMany (q : Q) (k : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:k] do
    acc := acc + q.f q.xs
  return acc

@[noinline] def headOr0 : List Nat → Nat
  | [] => 0
  | x :: _ => x

def main (args : List String) : IO Unit := do
  let n := (args.headD "300").toNat!
  let q : Q := ⟨Nat, List.range n, headOr0⟩
  IO.println (q.applyMany n + headOr0 [n])
