/-! Runtime test: BA-09's growing list (RtReprExistRepack), kept in a user
record (design review of the layout redesign, performance, DRP-04). `St`
has no type parameter, so its field `xs` is always a `List Nat`; `Packed`
(α is a field) holds a `List lcAny`. Every step stores the list into both,
so with two layouts one of the two stores converts the whole list: O(i)
at step i, O(n^2) in the loop (16012037 allocations at n = 4000, natively
19070). A design that keeps a typed record field typed and the package
uniform still converts here. The output is checked here; the allocations
by tests/runtime/alloc-check.sh (RtReprRecRepack.alloc). -/
structure St where
  xs : List Nat
  steps : Nat

structure Packed where
  α : Type
  xs : List α
  f : α → Nat

@[noinline] def Packed.headVal (p : Packed) : Nat :=
  match p.xs with
  | [] => 0
  | x :: _ => p.f x

@[noinline] def St.push (s : St) (i : Nat) : St := { s with xs := i :: s.xs, steps := s.steps + 1 }

@[noinline] def loop : Nat → St → Nat → Nat
  | 0, s, acc => acc + s.xs.length + s.steps
  | n + 1, s, acc =>
    let s := s.push n
    loop n s (acc + Packed.headVal ⟨Nat, s.xs, id⟩)

def main (args : List String) : IO Unit := do
  let n := (args.headD "300").toNat!
  IO.println s!"{loop n ⟨[], 0⟩ 0}"
