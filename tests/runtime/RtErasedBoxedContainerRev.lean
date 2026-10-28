/-! Runtime test (bug hunt of rule 4's flow analysis, 2026-10-27, HsErased6,
and its review): the other direction of `RtErasedBoxedContainer`. Uniform
code (`buildPk`, reached only through a function value, so its type
argument is a variable there) builds an `Array σ` (mono `Array lcAny`) of a
value `mkV g : S` that completes at its first domain, and boxes the array
whole into a type-valued field; typed code casts it to `Array T` (`T`'s
first domain erased) and applies the element at `T`. The second part does
the same with the array inside a generic structure `G σ`, read as a
structure `WT` of its own whose field is an `Array T`. Natively `mkV`'s
body runs once per part, at `f Nat`. In a program that casts, the analysis
boxes and unboxes each type argument of an extern instance that the code
calls (`externElems`): the read at `T` (`Array.get!` at `T`) unboxes `T`,
which meets `S`, boxed where it became `σ`. Before, `mkV`'s body ran at
each application in `twiceApply` (twice per part). -/
set_option linter.unusedVariables false

opaque Fam2 : Type 1
axiom hF2 : Fam2 = Type

-- completes at its `α` argument (the result type is a type variable)
@[noinline] def mkV {α : Type 1} {β : Type} (b : β) : α → β :=
  fun _ => dbgTrace "mkV body" fun _ => b

abbrev S := Fam2 → Nat → Nat
abbrev T := Type → Nat → Nat
instance : Inhabited T := ⟨fun _ n => n⟩

structure Pk where
  τ : Type 1
  σ : Type 1
  h : τ = Array σ
  v : τ

-- generic: reached only through a function value (its type argument is a
-- variable there), so its uniform instance builds the array
@[noinline] def buildPk {σ : Type 1} (x : σ) : Pk := ⟨Array σ, σ, rfl, #[x]⟩

structure Builder where
  run : (σ : Type 1) → σ → Pk

def bld : Builder := ⟨fun σ x => buildPk x⟩

@[noinline] def mkPk (g : Nat → Nat) : {p : Pk // p.σ = T} :=
  ⟨bld.run S (mkV (α := Fam2) g), congrArg (fun X : Type 1 => X → Nat → Nat) hF2⟩

@[noinline] def twiceApply (w : Nat → Nat) : Nat := w 1 + w 2
@[noinline] def useT (f : T) : Nat := twiceApply (f Nat)

@[noinline] def readPk (q : {p : Pk // p.σ = T}) : Nat :=
  let a : Array T := cast (q.1.h.trans (congrArg Array q.2)) q.1.v
  useT a[0]!

-- The array inside a generic structure, read as a structure of its own.
structure G (σ : Type 1) where
  arr : Array σ
  n : Nat

structure WT where
  arr : Array T
  n : Nat

axiom hGW : G T = WT

structure PkG where
  τ : Type 1
  σ : Type 1
  h : τ = G σ
  v : τ

@[noinline] def buildPkG {σ : Type 1} (x : σ) : PkG := ⟨G σ, σ, rfl, ⟨#[x], 2⟩⟩

structure BuilderG where
  run : (σ : Type 1) → σ → PkG

def bldG : BuilderG := ⟨fun σ x => buildPkG x⟩

@[noinline] def mkPkG (g : Nat → Nat) : {p : PkG // p.σ = T} :=
  ⟨bldG.run S (mkV (α := Fam2) g), congrArg (fun X : Type 1 => X → Nat → Nat) hF2⟩

@[noinline] def readPkG (q : {p : PkG // p.σ = T}) : Nat :=
  let w : WT := cast ((q.1.h.trans (congrArg G q.2)).trans hGW) q.1.v
  useT w.arr[0]! + w.n

def main : IO Unit := do
  IO.println (readPk (mkPk (· + 10)))
  IO.println (readPkG (mkPkG (· + 20)))
