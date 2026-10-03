/-! Runtime test: an `unsafe def` whose name ends in `_unsafe_rec` (the
name of the code Lean generates for a `partial def`, which in Lean 4.33 is
not `unsafe`) casts an existential payload of one structure to another of
the same layout. Its `unsafe` makes the program one that can cast (plan
§5.1, `programCasts`), whatever its name; the `partial def` makes no
difference. -/

structure Pkg where
  α : Type
  v : α
  tag : Nat

structure P1 where
  x : Nat
  s : String

structure P2 where
  y : Nat
  t : String
deriving Inhabited

@[noinline] unsafe def Rd._unsafe_rec (p : Pkg) : P2 := unsafeCast p.v
@[implemented_by Rd._unsafe_rec] opaque Rd (p : Pkg) : P2

partial def loop (n : Nat) : Nat := if n > 100 then n else loop (n * 2 + 1)

@[noinline] def mk (n : Nat) : Pkg := ⟨P1, ⟨n + 5, "one"⟩, n⟩

def main (args : List String) : IO Unit := do
  let p : Pkg := mk args.length
  let q := Rd p
  IO.println s!"{q.y} {q.t} {loop args.length}"
