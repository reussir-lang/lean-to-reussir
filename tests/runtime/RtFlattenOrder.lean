/-! Runtime test: optimization `flatten-structs` and a call's result used
whole inside a join point's body and given to that join point (review of
the pass, round 4, F3: built at the jump and again in the body). A result
the declaration uses whole stays whole there (`AState.builtCalls`: the
call goes through the wrapper), so one pair per step, as native
(`RtFlattenOrder.alloc`; `same=true`). -/
@[noinline] def mkP (i : Nat) : Nat × Nat := (i, i + 1)
@[noinline] def readP (i : Nat) : Nat := (mkP i).1 + (mkP (i + 1)).2

@[noinline] def twoUsesRev (n : Nat) : Array (Nat × Nat) × Array (Nat × Nat) := Id.run do
  let mut a := Array.mkEmpty n
  let mut b := Array.mkEmpty n
  for i in [0:n] do
    let r := mkP i
    let q := if i % 2 == 0 then r else (i, i)
    b := b.push q
    a := a.push r
  return (a, b)

unsafe def main (args : List String) : IO Unit := do
  match args with
  | [k] =>
    let n := k.toNat!
    let (a, b) := twoUsesRev n
    IO.println s!"{a.size} {b.size} {readP 3}"
  | _ =>
    let (a, b) := twoUsesRev 3
    IO.println s!"twoUsesRev {a} {b} {readP 1} same={ptrAddrUnsafe a[0]! == ptrAddrUnsafe b[0]!}"
