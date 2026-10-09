/-! Runtime test (`programCasts`, review of the walk's `@[csimp]` fix): a
`local` `@[csimp]` replaces `asP2` by `asP2Fast` in this module's compiled
code, and `asP2Fast` is implemented by an `unsafe` declaration that reads an
existential payload of one structure as another of the same layout
(inlined: `asP2Impl`). Natively the same object is read. A `local`
attribute is not saved in the module's `.olean`, so the `@[csimp]` state
after import (`CSimp.ext`) lacks the replacement: the walk did not reach
`asP2Fast`, the program counted as one that cannot cast, and the program
lean2rr built stopped with "INTERNAL PANIC: unreachable code has been
reached". The walk now starts also from `g` for each constant of the
program's modules stated as `@f = @g` (`programCsimps`).
`RtCastCsimpScoped`: the same with a `scoped` `@[csimp]`. -/

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
theorem asP2_eq : @asP2 = @asP2Fast := rfl
attribute [local csimp] asP2_eq

@[noinline] def mk (n : Nat) : Pkg := ⟨P1, ⟨n + 5, "one"⟩⟩

def main (args : List String) : IO Unit := do
  let ps := [mk args.length, mk 3]
  IO.println s!"{ps.foldl (fun acc p => acc + (asP2 p).y + (asP2 p).t.length) 0}"
