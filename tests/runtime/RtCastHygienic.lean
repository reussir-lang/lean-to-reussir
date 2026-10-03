/-! Runtime test: declarations with hygienic names (made by a macro:
`helper._@.RtCastHygienic._hyg.N`) in the program. lean2rr finds the
declarations they come from (`sourceDecls`, plan §5.1 `programCasts`)
without error, and an `unsafe` cast among them makes the program one that
can cast: an existential payload of one structure read as another of the
same layout. -/

structure Pkg where
  α : Type
  v : α

structure P1 where
  x : Nat
  s : String

structure P2 where
  y : Nat
  t : String
deriving Inhabited

open Lean in
macro "mkdefs" : command => `(
  @[noinline] def helper (n : Nat) : List Nat := List.range (n % 7 + 3)
  @[noinline] unsafe def rd (p : Pkg) : P2 := unsafeCast p.v
  @[implemented_by rd] opaque $(mkIdent `Rd) (p : Pkg) : P2
  def $(mkIdent `runIt) (n : Nat) : IO Unit := do
    IO.println s!"{(helper n).map (· * 2)}"
    let q := $(mkIdent `Rd) ⟨P1, ⟨n + 5, "one"⟩⟩
    IO.println s!"{q.y} {q.t}")
mkdefs

def main (args : List String) : IO Unit := runIt args.length
