/-! Runtime test (blowup audit, semantics probe SemRefAlias): one `IO.Ref
(List Nat)` and one `ST.Ref σ (List Nat)` are reached through a typed view,
an existential package (uniform code) and a dependent field (`List
ty.denote`); updates through each view must be visible through every other,
and the reference must stay one cell (`ptrEq`). -/
inductive Ty | nat | str

@[reducible] def Ty.denote : Ty → Type
  | .nat => Nat
  | .str => String

structure PkR where
  α : Type
  r : IO.Ref (List α)
  x : α

structure DR where
  t : Ty
  r : IO.Ref (List t.denote)

@[noinline] def pushU (p : PkR) : IO Unit := p.r.modify (p.x :: ·)
@[noinline] def setU (p : PkR) : IO Unit := do
  let l ← p.r.get
  p.r.set (l ++ [p.x])
@[noinline] def lenU (p : PkR) : IO Nat := return (← p.r.get).length
@[noinline] def pushD (d : DR) (i : Nat) : IO Unit :=
  match d with
  | ⟨.nat, r⟩ => r.modify (i :: ·)
  | ⟨.str, r⟩ => r.modify (toString i :: ·)
@[noinline] def getD (d : DR) : IO (List Nat) :=
  match d with
  | ⟨.nat, r⟩ => r.get
  | ⟨.str, _⟩ => pure []
structure PkR2 where
  α : Type
  r1 : IO.Ref (List α)
  r2 : IO.Ref (List α)

@[noinline] def sameU (p : PkR2) : IO Bool := p.r1.ptrEq p.r2
@[noinline] def sameD (d : DR) (r : IO.Ref (List Nat)) : IO Bool :=
  match d with
  | ⟨.nat, r'⟩ => r'.ptrEq r
  | ⟨.str, _⟩ => pure false

structure PkS (σ : Type) where
  α : Type
  r : ST.Ref σ (List α)
  x : α

@[noinline] def pushS {σ : Type} (p : PkS σ) : ST σ Unit := p.r.modify (p.x :: ·)

def stTest (n : Nat) : List Nat := runST fun _ => do
  let r ← ST.mkRef ([] : List Nat)
  let p : PkS _ := ⟨Nat, r, 7⟩
  for i in [0:n] do
    pushS p
    r.modify (i :: ·)
  r.get

def main : IO Unit := do
  let r ← IO.mkRef ([] : List Nat)
  let p : PkR := ⟨Nat, r, 5⟩
  let q : PkR := ⟨Nat, r, 6⟩
  let d : DR := ⟨.nat, r⟩
  pushU p
  r.modify (1 :: ·)
  pushD d 2
  pushU q
  setU p
  IO.println s!"typed {← r.get}"
  IO.println s!"uniform len {← lenU p} {← lenU q}"
  IO.println s!"dependent {← getD d}"
  IO.println s!"ptrEq uniform {← sameU ⟨Nat, r, r⟩} dependent {← sameD d r}"
  IO.println s!"ST {stTest 3}"
