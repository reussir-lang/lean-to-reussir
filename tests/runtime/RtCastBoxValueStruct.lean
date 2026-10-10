/-! Runtime test: a `Box` read at a `[value]` struct in a program that
casts (hunt HBOX2-02). `U` is an `unsafe` one-field inductive: natively a
constructor object with one object field, in lean2rr a `[value]` struct
over `Nat`. A `P` read as a `U` reads `P`'s first object field natively:
`5`, and `[5, 7]` for a list of `P` read as a list of `U`. lean2rr's typed
cast converts by constructor (`asU`). Through a box (the list's elements),
its unboxing at `U` read only `U`'s field (a `Nat`), so a `P` there
panicked (unreachable code); now what the field's unboxing does not read
goes to the generated cast function at `U`, whose field is taken. The
first lines box and unbox `[value]` structs of this program that casts,
which keep their fields' own unboxing in line: over a `Float` and a
`UInt64` from 2^63 (cells, which the cast function has no arm for) and
over a structure (`W`). -/
unsafe inductive U where
  | mk : Nat → U

unsafe def U.get : U → Nat | .mk n => n

structure P where
  a : Nat
  b : String

unsafe inductive UF where
  | mk : Float → UF

unsafe def UF.get : UF → Float | .mk x => x

unsafe inductive UU where
  | mk : UInt64 → UU

unsafe def UU.get : UU → UInt64 | .mk x => x

structure W where
  a : Nat
  b : Nat

unsafe inductive UW where
  | mk : W → UW

unsafe def UW.get : UW → Nat | .mk w => w.a * 10 + w.b

@[noinline] unsafe def mkUFs (k : Nat) : List UF := [.mk (1.5 + k.toFloat), .mk 2.25]
@[noinline] unsafe def mkUUs (k : Nat) : List UU := [.mk (9223372036854775813 + k.toUInt64), .mk 7]
@[noinline] unsafe def mkUWs (k : Nat) : List UW := [.mk ⟨1 + k, 2⟩, .mk ⟨3, 4⟩]

@[noinline] unsafe def asU (p : P) : U := unsafeCast p
@[noinline] unsafe def asUs (ps : List P) : List U := unsafeCast ps

unsafe def main (args : List String) : IO Unit := do
  let k := args.length
  IO.println ((mkUFs k).map UF.get)
  IO.println ((mkUUs k).map UU.get)
  IO.println ((mkUWs k).map UW.get)
  IO.println (asU ⟨5 + k, "x"⟩).get
  IO.println ((asUs [⟨5 + k, "x"⟩, ⟨7, "y"⟩]).map U.get)
