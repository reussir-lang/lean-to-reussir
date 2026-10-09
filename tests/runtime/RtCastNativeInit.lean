import CastNativeInitDep

/-! Runtime test (`programCasts`, axioms of native evaluation): the
statement of `flagTrue`'s axiom reaches `flag`, which an `initialize` action
of the companion module `CastNativeInitDep` sets. The action runs when a
module imports that one, so the value can differ between the builds of two
modules: with `← return (← IO.getEnv "V").isSome`, a module built with `V`
set proves `(flag && true) = true` by `native_decide`, one built without
proves `(flag || false) = false`, and a third module that imports both
proves `False` (review of 7732aaef; native reads the payload of one
structure as another, lean2rr counted the program as one that cannot cast
and stopped at an unboxing). The test suite builds every module in one
environment, so here the action is constant and nothing contradicts; the
axiom is not exempt all the same (`nativeEvalWalk` stops at a constant
with an init function). `RtCastNativeInit.l2r-debug`: the program casts.
`checkedFlag`'s value mentions `flagTrue`. -/

theorem flagTrue : (flag && true) = true := by native_decide

@[noinline] def checkedFlag (n : Nat) : {b : Bool // (b && true) = true} :=
  if n == 1000 then ⟨true, rfl⟩ else ⟨flag, flagTrue⟩

def main (args : List String) : IO Unit := do
  IO.println s!"{(checkedFlag args.length).val} {flag}"
