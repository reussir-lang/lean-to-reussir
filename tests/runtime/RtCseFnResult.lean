/-! Runtime test: a call that Lean's mono `cse` merges across types whose
result holds a function (`Option (α → α)` at `Nat` and at `String`). Lean
runs the call once; lean2rr does not align it to the earlier call's types
(XT-6), because a function value there, one closure natively, has no
conversion between `Nat → Nat` and `String → String` here (review XT6-01):
the call runs twice and its trace prints twice. A known difference (plan
§10, "Merging after erasure"). Lean does not fix how often a trace in pure
code prints, so the test records both runs' stderr
(`RtCseFnResult.native.err`, `RtCseFnResult.l2r.err`) and fails if either
changes. -/

@[noinline] def mkO {α : Type} (n : Nat) : Option (α → α) :=
  dbgTrace s!"mkO {n}" fun _ => some id
@[noinline] def useN (o : Option (Nat → Nat)) : Nat := match o with | some f => f 5 | none => 0
@[noinline] def useS (o : Option (String → String)) : String := match o with | some f => f "s" | none => ""

def run (n : Nat) : String := s!"{useN (mkO n)} {useS (mkO n)}"

def main (args : List String) : IO Unit := IO.println (run args.length)
