/-! Runtime test (blowup audit, semantics probe SemCowPlaceholder): an array
that crossed into uniform code is updated there (`Array.modify`, which
stores Lean's `box(0)` placeholder in the slot while the function runs,
`set!`, `push`); the caller's typed array, still alive, must be unchanged
(copy-on-write), and the updated value must read back correctly at the typed
view (dependent field). -/
inductive Ty | nat | str

@[reducible] def Ty.denote : Ty → Type
  | .nat => Nat
  | .str => String

structure PkA where
  α : Type
  a : Array (List α)
  x : α

structure Col where
  t : Ty
  a : Array (List t.denote)

@[noinline] def modU (p : PkA) : PkA := ⟨p.α, (p.a.modify 0 (p.x :: ·)).push [p.x], p.x⟩
@[noinline] def lensU (p : PkA) : List Nat := p.a.toList.map List.length
@[noinline] def modD (c : Col) (i : Nat) : Col :=
  match c with
  | ⟨.nat, a⟩ => ⟨.nat, (a.modify 1 (i :: ·)).set! 0 [i, i]⟩
  | ⟨.str, a⟩ => ⟨.str, a.modify 1 (toString i :: ·)⟩
@[noinline] def readD (c : Col) : List (List Nat) :=
  match c with
  | ⟨.nat, a⟩ => a.toList
  | ⟨.str, _⟩ => []

def main : IO Unit := do
  let a : Array (List Nat) := #[[1], [2, 3]]
  let p := modU ⟨Nat, a, 9⟩
  IO.println s!"typed after uniform modify {a}"
  IO.println s!"uniform lengths {lensU p}"
  let c := modD ⟨.nat, a⟩ 4
  IO.println s!"typed after dependent modify {a}"
  IO.println s!"dependent {readD c}"
  let c2 := modD c 5
  IO.println s!"dependent twice {readD c2} first still {readD c}"
