/-! Runtime test: polymorphic recursion through a monad transformer
(blowup audit, probe MonadGrow, checked and not a problem): `grow` calls
itself at `StateT Nat m`, so the monad grows at each level and the
recursion goes to the uniform instance. The outer state, a list of n
numbers, is read and extended at every level; it must not be converted at
each level: the allocations grow with n as native's do (by the list
itself), not by n per level. Arguments: K N (default 5 100). The output is
checked here; the allocations by tests/runtime/alloc-check.sh
(RtReprMonadGrow.alloc). -/
def grow {m : Type → Type} [Monad m] [MonadStateOf (List Nat) m] : Nat → m Nat
  | 0 => do return (← get).length
  | k + 1 => do
    let r ← (grow (m := StateT Nat m) k).run' k
    modify fun (l : List Nat) => r :: l
    return r + 1

def main (args : List String) : IO Unit := do
  let k := (args.headD "5").toNat!
  let n := (args.getD 1 "100").toNat!
  let (r, s) := (grow (m := StateM (List Nat)) k).run (List.range n)
  IO.println s!"{r} {s.length} {s.headD 0}"
