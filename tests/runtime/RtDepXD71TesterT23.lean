/-! Runtime test: case `D71TesterT23` of the shared dependent-type corpus
(programs built by another translator's team and checked against native
Lean). It checks: R42c noSplit: merged calls of a generic with an lcAny
result slot: pure (split), dbgTrace and panic (kept one call). The merged
calls `mkP n` and `mkT n`, whose results hold functions of `α`, go to the
instance at `lcAny`, so `mkT`'s trace prints once, as natively (it printed
twice through lean2rr when the calls ran apart). -/
@[noinline] def mkP {α : Type} (n : Nat) : Option (α → α) := if n > 1000000 then none else some id
@[noinline] def mkT {α : Type} (n : Nat) : List (α → α) := dbgTrace s!"mkT {n}" fun _ => [id, id]
@[noinline] def mkE {α : Type} (n : Nat) : Option (List α) := if n == 3 then panic! "three" else some []
@[noinline] def useN (o : Option (Nat → Nat)) : Nat := match o with | some f => f 5 | none => 0
@[noinline] def useS (o : Option (String → String)) : String := match o with | some f => f "s" | none => "-"
@[noinline] def lenN (o : List (Nat → Nat)) : Nat := o.length + (o.map (· 1)).foldl (· + ·) 0
@[noinline] def lenS (o : List (String → String)) : String := String.join (o.map (· "x"))
@[noinline] def eN (o : Option (List Nat)) : Nat := match o with | some l => l.length + 1 | none => 0
@[noinline] def eS (o : Option (List String)) : String := match o with | some l => s!"{l}" | none => "none"
def run (n : Nat) : String := s!"{useN (mkP n)} {useS (mkP n)} {lenN (mkT n)} {lenS (mkT n)} {eN (mkE n)} {eS (mkE n)}"
def main (args : List String) : IO Unit := IO.println (run args.length)
