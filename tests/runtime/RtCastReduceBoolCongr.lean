/-! Runtime test (`programCasts`, kernel evaluation): `congrArg` applied to
`Lean.reduceBool` and `Eq.refl lieAux` has the type `reduceBool lieAux =
reduceBool lieAux`, which the kernel accepts as `true = false` by running
the compiled code of `lieAux` (`true`, through `lie`'s `implemented_by`
target `lieImpl`) and unfolding `falseC`. No `ofReduceBool`: `#print
axioms` shows only `Lean.trustCompiler`. The proof of `False` reads an
existential payload of one structure as another of the same layout
(`asP2`), as an `unsafeCast` does natively. `programCasts` counts
`reduceBool` and `reduceNat` too, in values and in types
(`isKernelEvalConst`). Before, the program counted as one that cannot cast
and stopped with "INTERNAL PANIC: unreachable code has been reached"
(review of 55514050). `RtCastReduceBoolCongr.l2r-debug`: the program
casts. -/

set_option linter.deprecated false

def lieImpl : Bool := true

@[implemented_by lieImpl] def lie : Bool := false

def lieAux : Bool := lie

def falseC : Bool := false

theorem lieTrue : lie = true := by
  have h := @congrArg Bool Bool lieAux falseC Lean.reduceBool (Eq.refl lieAux)
  have h2 : true = false := h
  exact absurd h2 (by decide)

structure P1 where
  x : Nat
  s : String

structure P2 where
  y : Nat
  t : String

structure Pkg where
  α : Type
  v : α

theorem anyEq (a b : Type) : a = b := absurd lieTrue (by decide)

@[noinline] def asP2 (p : Pkg) : P2 := cast (anyEq p.α P2) p.v

@[noinline] def mk (n : Nat) : Pkg := ⟨P1, ⟨n + 5, "one"⟩⟩

def main (args : List String) : IO Unit := do
  let ps := [mk args.length, mk 3]
  IO.println s!"{ps.foldl (fun acc p => acc + (asP2 p).y + (asP2 p).t.length) 0}"
