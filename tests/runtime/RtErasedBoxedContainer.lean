/-! Runtime test (bug hunt of rule 4's flow analysis, 2026-10-27, HsErased4,
and its review, HsErased7 and HsErased8): a function value boxed only as
part of a whole container. `mkV g : S`, with `S = Fam2 → Nat → Nat`
(`Fam2` opaque, so the domain stays `lcAny`), completes at its first
argument (its result type is a type variable). It goes into a container
at `S`, which is stored whole in a type-valued field and read back with
its element type unknown (`lcAny`); the element is cast to
`T = Type → Nat → Nat` (`hF2 : Fam2 = Type`), whose first domain is
erased, and applied there. Natively `mkV`'s body runs once per part, at
`f Nat`. The parts: an `Array S` read as `Array p.σ` (mono `Array lcAny`);
a `Task S` read as `Task p.σ`; an `Array S` in a structure `W` of its own
(its constructor takes the array at its own type) read as a generic
`G p.σ` (mono `G lcAny`); a `List S` that `Array.toList` fills (no
constructor of the program) read as `List p.σ`. In a program that casts,
rule 4's analysis boxes and unboxes each type argument of an extern
instance that the code calls (`Array.push` at `S`, `Task.pure` at `S`,
`Array.toList` at `S`; `externElems`), since the runtime holds those
elements in boxes, so `S` meets `T` through the `Box` and `T` keeps its
erased domain. Before, nothing linked them, `T`'s domain was phantom, and
`mkV`'s body ran at each application in `twiceApply` (twice per part). -/
set_option linter.unusedVariables false

opaque Fam2 : Type 1
axiom hF2 : Fam2 = Type

-- completes at its `α` argument (the result type is a type variable)
@[noinline] def mkV {α : Type 1} {β : Type} (b : β) : α → β :=
  fun _ => dbgTrace "mkV body" fun _ => b

abbrev S := Fam2 → Nat → Nat
abbrev T := Type → Nat → Nat

structure Pk where
  τ : Type 1
  σ : Type 1
  h : τ = Array σ
  h2 : σ = T
  v : τ

@[noinline] def mkPk (g : Nat → Nat) : Pk :=
  let arr : Array S := (#[] : Array S).push (mkV (α := Fam2) g)
  ⟨Array S, S, rfl, congrArg (fun X : Type 1 => X → Nat → Nat) hF2, arr⟩

@[noinline] def twiceApply (w : Nat → Nat) : Nat := w 1 + w 2
@[noinline] def useT (f : T) : Nat := twiceApply (f Nat)

@[noinline] def readPk (p : Pk) : Nat :=
  let a : Array p.σ := cast p.h p.v
  match a[0]? with
  | some x => useT (cast p.h2 x)
  | none => 0

-- The same through a whole `Task S`.
structure PkT where
  τ : Type 1
  σ : Type 1
  h : τ = Task σ
  h2 : σ = T
  v : τ

@[noinline] def mkPkT (g : Nat → Nat) : PkT :=
  let t : Task S := Task.pure (mkV (α := Fam2) g)
  ⟨Task S, S, rfl, congrArg (fun X : Type 1 => X → Nat → Nat) hF2, t⟩

@[noinline] def readPkT (p : PkT) : Nat :=
  let t : Task p.σ := cast p.h p.v
  useT (cast p.h2 t.get)

-- An `Array S` inside a structure of its own, read as a generic one.
structure W where
  arr : Array S
  n : Nat

structure G (σ : Type 1) where
  arr : Array σ
  n : Nat

axiom hWG : W = G S

structure PkG where
  τ : Type 1
  σ : Type 1
  h : τ = G σ
  h2 : σ = T
  v : τ

@[noinline] def mkPkG (g : Nat → Nat) : PkG :=
  let w : W := ⟨(#[] : Array S).push (mkV (α := Fam2) g), 1⟩
  ⟨W, S, hWG, congrArg (fun X : Type 1 => X → Nat → Nat) hF2, w⟩

@[noinline] def readPkG (p : PkG) : Nat :=
  let gv : G p.σ := cast p.h p.v
  match gv.arr[0]? with
  | some x => useT (cast p.h2 x) + gv.n
  | none => 0

-- A `List S` that `Array.toList` fills.
structure PkL where
  τ : Type 1
  σ : Type 1
  h : τ = List σ
  h2 : σ = T
  v : τ

@[noinline] def mkPkL (g : Nat → Nat) : PkL :=
  let arr : Array S := (#[] : Array S).push (mkV (α := Fam2) g)
  ⟨List S, S, rfl, congrArg (fun X : Type 1 => X → Nat → Nat) hF2, arr.toList⟩

@[noinline] def readPkL (p : PkL) : Nat :=
  let l : List p.σ := cast p.h p.v
  match l with
  | x :: _ => useT (cast p.h2 x)
  | [] => 0

def main : IO Unit := do
  let p := mkPk (· + 10)
  IO.println (readPk p)
  let q := mkPkT (· + 20)
  IO.println (readPkT q)
  IO.println (readPkG (mkPkG (· + 30)))
  IO.println (readPkL (mkPkL (· + 40)))
