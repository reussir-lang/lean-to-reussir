/-!
Input of tests/runtime/allow-missing-check.sh (not a runtime test: no
`Rt` prefix). Refused externs of the program (an `opaque` re-declaring a
symbol of Lean's runtime: lean2rr never binds an extern of the program to
it) used directly, partially applied, as a closure, through an instance,
and through the `ptrAddrUnsafe` shortcut of the lowering. Under
`L2R_ALLOW_MISSING_EXTERNS=1` lean2rr generates the program, which must
not call the runtime's functions of these symbols (review REB-11): each
call is `l2r_refused_<declaration>`, which nothing defines.
-/

@[extern "lean_nat_gcd"]
opaque myGcd : Nat → Nat → Nat

@[extern "lean_ptr_addr"]
opaque myAddr {α : Type} (a : @& α) : USize

structure W where
  n : Nat

instance : Add W := ⟨fun a b => ⟨myGcd a.n b.n⟩⟩

@[noinline] def twice (f : Nat → Nat) (x : Nat) : Nat := f (f x)

def main (args : List String) : IO Unit := do
  let f := myGcd
  IO.println (twice (myGcd 12) (args.length + 18))
  IO.println ((List.range 3).map (myGcd 10))
  IO.println (f 12 18)
  IO.println ((⟨12⟩ + ⟨18⟩ : W).n)
  let a := #[args.length]
  IO.println (myAddr a == myAddr a)
