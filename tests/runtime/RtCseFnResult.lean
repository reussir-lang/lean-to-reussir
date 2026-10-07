/-! Runtime test: a call that Lean's mono `cse` merges across types whose
result holds a function (`Option (α → α)` at `Nat` and at `String`). Lean
runs the call once. The earlier call's instance makes a `Nat → Nat`
closure, which no conversion makes a `String → String` (review XT6-01), so
lean2rr ran the call twice and its trace printed twice (expectation files,
plan §10). Now both calls go to the instance at `lcAny`, whose closure
serves both types through wrappers: the trace prints once, as natively
(shared case A1028). -/

@[noinline] def mkO {α : Type} (n : Nat) : Option (α → α) :=
  dbgTrace s!"mkO {n}" fun _ => some id
@[noinline] def useN (o : Option (Nat → Nat)) : Nat := match o with | some f => f 5 | none => 0
@[noinline] def useS (o : Option (String → String)) : String := match o with | some f => f "s" | none => ""

def run (n : Nat) : String := s!"{useN (mkO n)} {useS (mkO n)}"

def main (args : List String) : IO Unit := IO.println (run args.length)
