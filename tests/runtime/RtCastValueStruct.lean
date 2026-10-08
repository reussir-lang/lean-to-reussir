/-! Runtime test: a `[value]` struct read through `unsafeCast` as another
inductive's constructor with one object field, and back. `U` is an `unsafe`
inductive and `R` a recursive one, so Lean does not erase them to their
field: natively each is a constructor object with one object field and
tag 0, as `Except.error e` is. lean2rr's types for them are
`struct [value] T_U(Nat)` and `struct [value] T_R(RVec<LAny>)`. Natively
the cast reads the field by its slot: `5`, `error 6`, `2` and `error 1`.
lean2rr converts constructor by constructor (`isObjectNominal` accepts a
`[value]` struct that Lean keeps as an object, so `ctorCastable` applies).
Before, it read the struct as its field (a `Nat` read as an `Except`): it
warned at translation and the cast panicked. -/
unsafe inductive U where
  | mk : Nat → U

unsafe def U.get : U → Nat | .mk n => n

inductive R where
  | mk : Array R → R

def R.size : R → Nat | .mk a => a.size

@[noinline] unsafe def asU (e : Except Nat String) : U := unsafeCast e
@[noinline] unsafe def asExcept (u : U) : Except Nat String := unsafeCast u
@[noinline] unsafe def asR (e : Except (Array R) String) : R := unsafeCast e
@[noinline] unsafe def rAsExcept (r : R) : Except (Array R) String := unsafeCast r

unsafe def main : IO Unit := do
  IO.println (asU (.error 5)).get
  match asExcept (.mk 6) with
  | .error n => IO.println s!"error {n}"
  | .ok s => IO.println s!"ok {s}"
  IO.println (asR (.error #[.mk #[], .mk #[]])).size
  match rAsExcept (.mk #[.mk #[]]) with
  | .error a => IO.println s!"error {a.size}"
  | .ok _ => IO.println "ok"
