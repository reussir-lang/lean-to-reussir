/-! Runtime test (`programCasts`): a `partial def` whose code reads an
existential payload of one structure as another of the same layout, through
a safe declaration implemented by an `unsafe` one (`asP2`, whose
implementation `asP2Impl` is inlined). Natively the same object is read.
A `partial def`'s value is only an inhabitant of its type; Lean compiles its
`_unsafe_rec` copy, so only there does `asP2` show. The walk of
`programCasts` did not take that copy: the program counted as one that
cannot cast, the box holding the `P1` had no arm for `P2`, and the program
lean2rr built stopped with "INTERNAL PANIC: unreachable code has been
reached" (the same program with a structural `def go` worked). It now
takes it. -/

structure P1 where
  x : Nat
  s : String

structure P2 where
  y : Nat
  t : String

structure Pkg where
  α : Type
  v : α

@[inline] unsafe def asP2Impl (p : Pkg) : P2 := unsafeCast p.v
@[implemented_by asP2Impl] def asP2 (_ : Pkg) : P2 := ⟨0, ""⟩

@[noinline] def mk (n : Nat) : Pkg := ⟨P1, ⟨n + 5, "one"⟩⟩

partial def go (ps : List Pkg) (acc : Nat) : Nat :=
  match ps with
  | [] => acc
  | p :: rest => go rest (acc + (asP2 p).y + (asP2 p).t.length)

def main (args : List String) : IO Unit := do
  IO.println s!"{go [mk args.length, mk 3] 0}"
