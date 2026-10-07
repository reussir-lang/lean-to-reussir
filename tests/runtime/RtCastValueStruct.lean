/-! Runtime test (known failure): a `[value]` struct read through
`unsafeCast` as another inductive's constructor with one object field, and
back. `U` (an `unsafe` inductive, which Lean keeps: lean2rr's
`struct [value] T_U(Nat)`) is natively a constructor object with one
object field and tag 0, as `Except.error e` is: natively the cast reads the
field by its slot, `5` and `error 6`. lean2rr has no conversion between a
`[value]` struct and an inductive of another constructor count
(`ctorCastable` takes shared records and enums only; `tryCoerce` reads the
struct as its field, here a `Nat` read as an `Except`): it warns at
translation and the cast panics. -/
unsafe inductive U where
  | mk : Nat → U

unsafe def U.get : U → Nat | .mk n => n

@[noinline] unsafe def asU (e : Except Nat String) : U := unsafeCast e
@[noinline] unsafe def asExcept (u : U) : Except Nat String := unsafeCast u

unsafe def main : IO Unit := do
  IO.println (asU (.error 5)).get
  match asExcept (.mk 6) with
  | .error n => IO.println s!"error {n}"
  | .ok s => IO.println s!"ok {s}"
