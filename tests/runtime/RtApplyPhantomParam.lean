/-! Runtime test: a function value whose parameter is itself a function
with an erased domain (`f : (α : Type) → α → α`, rule 4: no parameter for
`α` at run time, so the domain is `◾ → Box → Box` and its run-time type is
`Box → Box`), applied through the generated application function
`l2r_ap<j>_T` (hunt 3, conv). That function is shared by the types with
the same run-time type, so its parameters have run-time types. It passed
such an argument on as a value of type `Box → Box`: the conversion to the
target's parameter type `◾ → Box → Box` then wrapped it as a function
whose `◾` is an argument. The target applied `box(0)` for the value and
the value to the result: `addF 1 idA 5` gave `1`, not `6`.
- `apply2`, `apply1`: a partial application `addF k` (its `p` variant)
  applied to all its arguments, and to one of them.
- `e.f e.x`: a lambda that `Ex.map` builds where `α` is not known (type
  `Box → Nat`), applied to a value of `◾ → Box → Box`.
- `callIt (get e rfl).g`: that lambda read at `(◾ → Box → Box) → Nat`
  (its wrapped variant `w<S>`), applied to `idA`. -/

@[noinline] def useF (k : Nat) (f : (α : Type) → α → α) : Nat := f Nat 5 + k
@[noinline] def idA : (α : Type) → α → α := fun _ x => x
@[noinline] def twiceA : (α : Type) → (α → α) → α → α := fun _ g x => g (g x)

@[noinline] def apply2 (g : ((α : Type) → α → α) → Nat → Nat) (f : (α : Type) → α → α) (n : Nat) : Nat :=
  g f n
@[noinline] def apply1 (g : ((α : Type) → α → α) → Nat → Nat) (f : (α : Type) → α → α) : Nat → Nat :=
  g f

@[noinline] def addF (k : Nat) (f : (α : Type) → α → α) (n : Nat) : Nat := f Nat n + k

structure Ex where
  α : Type 1
  f : α → Nat
  x : α

def ex : Ex := ⟨((β : Type) → β → β), useF 1, idA⟩

@[noinline] def Ex.map (e : Ex) (g : Nat → Nat) : Ex := ⟨e.α, fun a => g (e.f a), e.x⟩

structure H where
  g : ((β : Type) → β → β) → Nat
  tag : Nat

@[noinline] def get (e : Ex) (h : e.α = ((β : Type) → β → β)) : H :=
  ⟨cast (congrArg (fun t => t → Nat) h) e.f, 0⟩

@[noinline] def callIt (g : ((β : Type) → β → β) → Nat) : Nat := g idA

def main : IO Unit := do
  IO.println (apply2 (addF 1) idA 5)
  IO.println ((apply1 (addF 2) idA) 7)
  IO.println (apply2 (addF 3) (fun β x => twiceA β id x) 9)
  let e := ex.map (· + 1)
  IO.println (e.f e.x)
  IO.println (callIt (get e rfl).g)
  IO.println (callIt (get ex rfl).g)
