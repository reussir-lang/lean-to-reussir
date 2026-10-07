/-! Runtime test: uniform code applies a function value of statically
unknown type to types and to data alike (rule 4, map C hazards H5 and H7).
In `runF`, `g : F b` has the mono type `lcAny`: lean2rr applies it as
`Box → Box`, to `box(0)` for each type argument and to the boxed data. The
value was boxed at its own type, whose erased domains are phantom
(`(α : Type) → List Nat → Nat`: no value runs after its `◾`) or kept
(`(α : Type) → (β : Type) → Nat`: `mkF` runs after the first `◾`): the
wrapper that views it as `Box → Box` drops the argument of a phantom
domain and passes `()` to a kept one. An extern partially applied at an
erased instance of its type variable (`Array.push` at `α := Type`, whose
element is `◾`) still passes its placeholder to the runtime. -/

universe u
@[noinline] def mkF {β : Type u} (n : Nat) (b : β) : (α : Type) → β :=
  fun _ => dbgTrace s!"mkF {n}" fun _ => b
@[noinline] def two (_ _ : Type) : Nat := dbgTrace "two" fun _ => 2
@[noinline] def inner (_ : Type) : Nat := dbgTrace "inner" fun _ => 3

def F : Bool → Type 1
  | true => (α : Type) → List Nat → Nat
  | false => (α : Type) → (β : Type) → Nat

@[noinline] def runF : (b : Bool) → F b → Nat
  | true, g => g Nat [1, 2, 3] + 10 * g String [4]
  | false, g => g Nat String

-- The same, with the value stored in a structure whose field type is not
-- known (an existential), and the application in a loop.
structure Pkg where
  b : Bool
  v : F b
@[noinline] def runPkg (p : Pkg) (k : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:k] do acc := acc + runF p.b p.v
  return acc

@[noinline] def lenT (xs : List Nat) : Nat := dbgTrace s!"lenT {xs.length}" fun _ => xs.length

-- `Array.push` at `α := Type` (its element is erased), partially applied.
@[noinline] def pushTy (xs : Array Type) : Type → Array Type := xs.push
@[noinline] def tys (k : Nat) : Nat := ((pushTy #[Nat, String] Bool).push (Fin k)).size + k

def main : IO Unit := do
  IO.println (runF true (fun _ xs => dbgTrace "lam" fun _ => xs.length))
  IO.println (runF true (fun _ => lenT))
  IO.println (runF false two)
  IO.println (runF false (mkF 7 inner))
  IO.println (runPkg ⟨true, fun _ xs => xs.length * 3⟩ 2)
  IO.println (runPkg ⟨false, mkF 8 inner⟩ 2)
  IO.println (runPkg ⟨false, two⟩ 2)
  IO.println (tys 5)
