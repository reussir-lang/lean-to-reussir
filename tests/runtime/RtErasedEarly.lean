/-! Runtime test: function values that run their body at an erased domain
that is not the last of their type (rule 4, map C hazards H3 and H4).
Lean eta-expands definitions and lambdas to the arity of their type, so
such a value comes from generic code whose result type is instantiated at
a function type: `mkF n b : (α : Type) → β` at `β := List Nat → Nat` runs
when the type is applied, and returns `b`. lean2rr keeps a unit domain at
such a point, so that the body runs once where Lean runs it, and the
function it returns is reused; values of the same type that do not run
there (`fun _ xs => …`) ignore that unit. The traces show when each body
runs and how many times; the applications are in loops of their own
(Lean's `cse` merges two applications to types). -/

universe u
@[noinline] def mkF {β : Type u} (n : Nat) (b : β) : (α : Type) → β :=
  fun _ => dbgTrace s!"mkF {n}" fun _ => b

structure Op where
  run : (α : Type) → List Nat → Nat

-- Bound once at a type, applied `k` times.
@[noinline] def loopL (g : List Nat → Nat) (k : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:k] do acc := acc + g [i, i]
  return acc
@[noinline] def useOp (o : Op) (k : Nat) : Nat := loopL (o.run Nat) k

-- Bound `k` times, each applied once.
@[noinline] def bindOp (o : Op) (k : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:k] do acc := acc + o.run String [i]
  return acc

@[noinline] def lenTrace (xs : List Nat) : Nat := dbgTrace s!"len {xs.length}" fun _ => xs.length

def ops : List Op :=
  [⟨mkF 1 lenTrace⟩, ⟨fun _ xs => dbgTrace "lambda" fun _ => xs.length * 2⟩, ⟨mkF 2 (fun xs => xs.length + 10)⟩]

-- An all-erased chain: `◾ → ◾ → Nat`, with values that run after the
-- first domain (`mkF` at `β := (γ : Type) → Nat`) and after the second.
structure TyFn where
  run : (α : Type) → (β : Type) → Nat
@[noinline] def two (_ _ : Type) : Nat := dbgTrace "two" fun _ => 2
@[noinline] def inner (_ : Type) : Nat := dbgTrace "inner" fun _ => 3
@[noinline] def loopT (g : (β : Type) → Nat) (k : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:k] do acc := acc + g String
  return acc
@[noinline] def useT (f : TyFn) (k : Nat) : Nat := loopT (f.run Nat) k

-- A function value with a data parameter after the erased one, partially
-- applied at the data before it: `mid 5` captures 5, and the unit the
-- type keeps for `mkF` is ignored.
@[noinline] def mid (x : Nat) (_ : Type) (xs : List Nat) : Nat := dbgTrace s!"mid {x}" fun _ => x + xs.length
@[noinline] def useMid (f : Nat → Op) (k : Nat) : Nat := useOp (f 5) k + bindOp (f 6) k

def main : IO Unit := do
  for o in ops do
    IO.println (useOp o 3)
    IO.println (useOp o 0)
    IO.println (bindOp o 2)
  IO.println (useT ⟨two⟩ 2)
  IO.println (useT ⟨mkF 3 inner⟩ 2)
  IO.println (useT ⟨mkF 4 inner⟩ 0)
  IO.println (useMid (fun n => ⟨mid n⟩) 2)
