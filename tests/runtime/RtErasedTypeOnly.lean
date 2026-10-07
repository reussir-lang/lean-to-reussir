/-! Runtime test: functions whose parameters are all erased (rule 4, map C
hazards H1 and H4), in a program where no function value runs its body
after the first of two erased domains. lean2rr removes erased parameters,
except that a function keeps one unit parameter for its trailing erased
ones, so that it stays a function; the type `◾ → ◾ → Nat` has a unit
domain only at its end (the first `◾` has no parameter at run time). The
traces show when each body runs and how many times. Lean eta-expands
definitions and lambdas to the arity of their type, so `two` and the
lambda run when both types are applied. The applications are in loops of
their own (`loopAp`): Lean's `cse` merges two applications to types (both
`g ◾` in mono code). -/

structure TyFn where
  run : (α : Type) → (β : Type) → Nat

@[noinline] def two (_ _ : Type) : Nat := dbgTrace "two" fun _ => 2

-- Bound at one type, applied `k` times to another.
@[noinline] def loopAp (g : (β : Type) → Nat) (k : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:k] do acc := acc + g String
  return acc
@[noinline] def useMany (f : TyFn) (k : Nat) : Nat := loopAp (f.run Nat) k

-- Bound `k` times, each applied once.
@[noinline] def bindMany (f : TyFn) (k : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:k] do acc := acc + f.run Nat Bool
  return acc

-- A function of one type parameter as a value, applied `k` times.
@[noinline] def apMany (h : (α : Type) → Nat) (k : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:k] do acc := acc + h Nat
  return acc
@[noinline] def tyOnly (_ : Type) : Nat := dbgTrace "tyOnly" fun _ => 5

-- A polymorphic constant: one type parameter, which Lean's arity
-- reduction keeps (otherwise it would be a constant), and a call of it
-- that is not a closed term: it runs at each call of `useEl`.
@[noinline] def el {α : Type} : List α := dbgTrace "el" fun _ => []
set_option compiler.extract_closed false in
@[noinline] def useEl (n : Nat) : Nat := (el (α := Nat)).length + n

def main : IO Unit := do
  IO.println (useMany ⟨two⟩ 3)
  IO.println (useMany ⟨two⟩ 0)
  IO.println (useMany ⟨fun _ _ => dbgTrace "lambda 2" fun _ => 7⟩ 2)
  IO.println (bindMany ⟨two⟩ 2)
  IO.println (apMany tyOnly 3)
  IO.println (apMany (fun _ => dbgTrace "lambda 1" fun _ => 6) 2)
  IO.println (apMany (two Nat) 0)
  IO.println (apMany (two Nat) 2)
  IO.println (useEl 1)
  IO.println (useEl 2)
