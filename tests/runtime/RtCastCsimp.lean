/-! Runtime test (`programCasts`): a `@[csimp]` theorem replaces `asP2` by
`asP2Fast` in compiled code, and `asP2Fast` is implemented by an `unsafe`
declaration that reads an existential payload of one structure as another of
the same layout (inlined: `asP2Impl`). Natively the same object is read.
Neither `main`'s value nor `asP2`'s mentions `asP2Fast`, and its code is
inlined, so the walk of `programCasts` did not reach it: the program counted
as one that cannot cast, the box holding the `P1` had no arm for `P2`, and
the program lean2rr built stopped with "INTERNAL PANIC: unreachable code
has been reached". The walk now takes the `@[csimp]` replacement of every
constant it reaches. -/

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
@[implemented_by asP2Impl] def asP2Fast (_ : Pkg) : P2 := ⟨0, ""⟩
def asP2 (_ : Pkg) : P2 := ⟨0, ""⟩
@[csimp] theorem asP2_eq : @asP2 = @asP2Fast := rfl

@[noinline] def mk (n : Nat) : Pkg := ⟨P1, ⟨n + 5, "one"⟩⟩

def main (args : List String) : IO Unit := do
  let ps := [mk args.length, mk 3]
  IO.println s!"{ps.foldl (fun acc p => acc + (asP2 p).y + (asP2 p).t.length) 0}"
