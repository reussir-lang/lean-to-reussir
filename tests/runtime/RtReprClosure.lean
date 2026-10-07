/-! Runtime test (blowup audit, semantics probe SemClosure): a partial
application (`add3 1`, two arguments missing) and a closure travel through
an existential package (uniform code applies them at `L2RBox`); the target
must run only when its last argument arrives, once per full application, in
native order (dbgTrace order on stderr). The same closure crosses back to
the typed view (dependent field) and is applied there. -/
inductive Ty | nat | str

@[reducible] def Ty.denote : Ty → Type
  | .nat => Nat
  | .str => String

structure PkF where
  α : Type
  f : α → α → α
  g : Nat → α
  toN : α → Nat

structure DF where
  t : Ty
  f : t.denote → t.denote → t.denote

@[noinline] def add3 (a b c : Nat) : Nat := dbgTrace s!"add3 {a} {b} {c}" fun _ => a + b + c

@[noinline] def useF (p : PkF) : Nat :=
  let h := p.f (p.g 2)
  p.toN (dbgTrace "between" fun _ => p.f (h (p.g 3)) (p.g 4))

@[noinline] def backD (d : DF) (x : Nat) : Nat :=
  match d with
  | ⟨.nat, f⟩ => let h := f x; dbgTrace "typed partial" fun _ => h 10
  | ⟨.str, _⟩ => 0

def main : IO Unit := do
  let p : PkF := ⟨Nat, add3 1, fun i => dbgTrace s!"g {i}" fun _ => i, id⟩
  IO.println s!"uniform result {useF p}"
  IO.println s!"typed back {backD ⟨.nat, add3 100⟩ 20}"
