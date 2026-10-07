/-! Runtime test: a closed term in a branch that never runs is not
evaluated (a judged Lean 4.34.0 compiler bug that lean2rr does not
reproduce; plan §10, "A boxed constant in a branch that never runs is
computed at startup"). The dead arm
`[spin false 2.5]` boxes the closed term `spin false 2.5`, which never
returns. Natively Lean boxes it through an auxiliary constant
`K._boxed_const_1` (`ExplicitBoxing.mkCast`), which is not registered as a
closed term, so the module initializer computes it at startup
(`EmitC.emitDeclInit`), outside its branch: the native program hangs
before `main` (`RtDeadBoxedConst.native.out`, empty, and
`RtDeadBoxedConst.native.code`, 124: the test's `.pipe` stops each run
after 3 seconds). By Lean's semantics `K` is `[1.0]`. lean2rr's boxed
constants are once-cells computed at their first use, so it prints
`[1.000000]` (`RtDeadBoxedConst.l2r.out`, `.l2r.code` 0). The judge's
repro `c2/DeadSpinFalse.lean`; the same class as lean4 issue #1965, whose
fix (lazy closed terms, #12044) missed this path. -/

@[noinline] def flag (n : Nat) : Bool := n % 2 == 0
partial def spin (b : Bool) (x : Float) : Float := if b then x else spin b x

def K : List Float := match flag 3 with
  | true  => [spin false 2.5]
  | false => [1.0]

def main : IO Unit := IO.println s!"{K}"
