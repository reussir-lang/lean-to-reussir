/-! Runtime test (`programCasts`, the library's axioms of evaluation):
`Lean.ofReduceBool lieAux true rfl` proves `lie = true` because the kernel
runs the compiled code of `lieAux`, which calls `lie`'s `implemented_by`
target `lieImpl` (`true`); `lie`'s definition gives `false`. The proof of
`False` then reads an existential payload of one structure as another of
the same layout (`asP2`), as an `unsafeCast` does natively. `ofReduceBool`
and `reduceBool` (the constant the kernel evaluates; `ofReduceNat`,
`reduceNat`) are Lean's library, which the walk of `programCasts` does not
enter; it counts them when it reaches them (`isKernelEvalConst`; here
`reduceBool`, in `rfl`'s type, comes first). Until then the
program counted as one that cannot cast, the box holding the `P1` had no
arm for `P2`, and the program lean2rr built stopped with "INTERNAL PANIC:
unreachable code has been reached". `RtCastReduceBool.l2r-debug`: the
program casts. -/

set_option linter.deprecated false

def lieImpl : Bool := true

@[implemented_by lieImpl] def lie : Bool := false

def lieAux : Bool := lie

theorem lieTrue : lie = true := Lean.ofReduceBool lieAux true rfl

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
  IO.println s!"{ps.foldl (fun acc p => acc + (asP2 p).y + (asP2 p).t.length) 0} {lie}"
