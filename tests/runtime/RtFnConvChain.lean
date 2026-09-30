/-! Runtime test: a function value converted through three or more
representations (adv3 RP3-3). A reference to a `Nat → Nat` read and written
back as `Nat → α` and `α → β` crosses `Nat → Nat`, `Nat → Box` and
`Box → Box`; each conversion converts the value from its original
representation, so it stays one wrapper deep (it used to gain three
wrappers per round, until applying it overflowed the stack), and after a
round trip it is the same object (`ptrEq`, as natively). -/

structure PkgA where
  α : Type
  r : IO.Ref (Nat → α)

structure PkgB where
  α : Type
  β : Type
  r : IO.Ref (α → β)

structure PkgC where
  α : Type
  r : IO.Ref (α → Nat)

structure Pkg2 where
  α : Type
  r : IO.Ref (Nat → α → Nat)

@[noinline] def touchA (p : PkgA) : IO Unit := do p.r.set (← p.r.get)
@[noinline] def touchB (p : PkgB) : IO Unit := do p.r.set (← p.r.get)
@[noinline] def touchC (p : PkgC) : IO Unit := do p.r.set (← p.r.get)
@[noinline] def touch2 (p : Pkg2) : IO Unit := do p.r.set (← p.r.get)

@[noinline] def same {α : Type} (a b : α) : Bool := unsafe ptrEq a b

def main (args : List String) : IO Unit := do
  let k := args.length
  let g := fun (x : Nat) => x + 1 + k
  let r ← IO.mkRef g
  -- one round: the same object again
  touchA ⟨Nat, r⟩
  touchB ⟨Nat, Nat, r⟩
  IO.println s!"one round: {same g (← r.get)} {(← r.get) 41}"
  -- many rounds through four representations, applied every 1000 rounds
  let mut acc := 0
  for i in [0:1000000] do
    touchA ⟨Nat, r⟩
    touchB ⟨Nat, Nat, r⟩
    touchC ⟨Nat, r⟩
    if i % 1000 == 0 then acc := acc + (← r.get) i
  IO.println s!"rounds: {acc} {same g (← r.get)} {(← r.get) 41}"
  -- a two-argument function, partially applied in between
  let h := fun (x y : Nat) => x * 10 + y + k
  let r2 ← IO.mkRef h
  for _ in [0:100000] do
    touch2 ⟨Nat, r2⟩
    touchA ⟨Nat → Nat, r2⟩
    touchB ⟨Nat, Nat → Nat, r2⟩
  let h' ← r2.get
  IO.println s!"two args: {same h h'} {h' 4 2} {(h' 7) 3}"
