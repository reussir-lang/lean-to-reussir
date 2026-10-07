/-! Runtime test: an association list of pairs updated in a loop
(`List (Nat × Nat)`, rebuilt up to the key; the probe of the dependent-type
work). The head pair is read at its type and, in the rebuilding branch,
put back into the new cell: lean2rr boxes the unboxed pair again there
(Reussir issue 39: passing the field's own box left a dead release of the
unboxed pair, which token reuse took as the new cell's donor, so every
rebuilt cell was allocated). The output is checked here; the allocations
by tests/runtime/alloc-check.sh (RtProbeBump.alloc). Argument: the number
of bumps (default 1000). -/
def bump : List (Nat × Nat) → Nat → List (Nat × Nat)
  | [], _ => []
  | (k', v) :: rest, k => if k == k' then (k', v + 1) :: rest else (k', v) :: bump rest k

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 1000
  let mut l : List (Nat × Nat) := (List.range 64).map (·, 0)
  for i in [0:n] do l := bump l (i % 64)
  IO.println s!"{l.foldl (fun a (_, v) => a + v) 0}"
