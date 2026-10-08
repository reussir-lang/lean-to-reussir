import Lean.Data.Position

/-!
A program of the `Lean` package that does not import `Std` and declares a
name that a module of `Std` declares too (`Std.Data.ByteSlice`'s
`ByteSlice`): natively no clash. lean2rr loads `Std` with such a program
(natively `lean_initialize()` initializes all of `Init` and `Std`), and the
two `ByteSlice`s clashed: lean2rr stopped ("environment already contains
'ByteSlice.start'"). Now `Std` is left out when it cannot be loaded (it has
no initializer), with a note, as is the shim's `Std` part.
-/

structure ByteSlice where
  start : Nat

def main : IO Unit :=
  IO.println (toString (ByteSlice.start ⟨3⟩) ++ toString (Lean.Position.mk 1 2))
