/-! Runtime test: the unit value read as a `Nat` through a package whose
value type is a field (`unsafeCast`). Natively the unit value is the
word `box(0)`, and a `Nat` read from it is 0: the program prints 0. -/
structure Pkg where
  α : Type
  v : α

@[noinline] unsafe def asNat (p : Pkg) : Nat := unsafeCast p.v

unsafe def main : IO Unit :=
  IO.println (asNat ⟨Unit, ()⟩)
