import CastNativeCrossLocalDep

/-! Runtime test (`programCasts`, axioms of native evaluation and the
`@[csimp]` theorems that act on them, `nativeExempt`): this module makes
`f_eq` of the companion module `CastNativeCrossLocalDep` (proved by
`sorry`, without the attribute there) a `local` `@[csimp]` theorem, which
no `.olean` records, so `native_decide` runs `g` (`true`) for `f`
(`false`) and adds a false axiom. Its proof of `False` reads an
existential payload of one structure as another of the same layout
(`asP2`), as an `unsafeCast` does natively. Every constant of the
program stated `@f = @g` is a candidate, in any module; one whose proof
can be false acts on every axiom whose evaluation reaches its `f`. A
candidate that may be `local` acted only in its own module: the program
counted as one that cannot cast and stopped with "INTERNAL PANIC:
unreachable code has been reached" (review of 55514050).
`RtCastNativeCrossLocal.l2r-debug`: the program casts. -/

attribute [local csimp] f_eq

theorem lie : f = true := by native_decide

structure P1 where
  x : Nat
  s : String

structure P2 where
  y : Nat
  t : String

structure Pkg where
  α : Type
  v : α

theorem anyEq (a b : Type) : a = b := absurd lie (by decide)

@[noinline] def asP2 (p : Pkg) : P2 := cast (anyEq p.α P2) p.v

@[noinline] def mk (n : Nat) : Pkg := ⟨P1, ⟨n + 5, "one"⟩⟩

def main (args : List String) : IO Unit := do
  let ps := [mk args.length, mk 3]
  IO.println s!"{ps.foldl (fun acc p => acc + (asP2 p).y + (asP2 p).t.length) 0}"
