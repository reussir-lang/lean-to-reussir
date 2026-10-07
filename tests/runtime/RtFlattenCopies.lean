/-! Runtime test: two shapes where optimization `flatten-structs` copied
an object that native Lean shares (review of the pass, round 3, findings A
and B). Without arguments it prints the values and the identities
(`ptrAddrUnsafe`: natively `same=true`); with a mode and n it makes n
calls or steps, for `RtFlattenCopies.alloc`:
- `store` (finding A): `tally` builds a new record at every step, so its
  parameter counts as fresh, but with an empty list it returns the
  caller's record itself. `tallyScore` reads the result field by field, so
  the result is a tuple, and `storeAll`, which stores the result, builds
  the record again from the tuple: one allocation per call that native
  does not make (the list is empty at 999 calls of 1000). Now a parameter
  that another declaration passes an existing object counts as existing
  (`AState.entryExisting`), so the result stays whole and the loop runs
  its first step in the wrapper, on the caller's record;
- `two` (finding B): the result of `mkP` (split, `readP` reads it field by
  field) is stored whole and also passed to a join point whose parameter
  is split and stored whole again: at every second step (where the join
  point gets `mkP`'s pair) two pairs where native has one. Now a call
  result used whole is an object that exists (`AState.builtCalls`): the
  join point takes it whole. -/

structure Best where
  key : Nat
  score : Nat
  hits : Nat
  deriving Inhabited

@[noinline] def tally : List (Nat × Nat) → Best → Best
  | [], b => b
  | (k, s) :: rest, b => tally rest { key := k, score := b.score + s, hits := b.hits + 1 }

@[noinline] def tallyScore (xs : List (Nat × Nat)) : Nat := (tally xs ⟨0, 0, 0⟩).score

@[noinline] def storeAll (b0 : Best) (n : Nat) : Array Best := Id.run do
  let mut out := Array.mkEmpty n
  for i in [0:n] do
    out := out.push (tally (if i % 1000 == 999 then [(i, 5)] else []) b0)
  return out

@[noinline] def mkP (i : Nat) : Nat × Nat := (i, i + 1)
@[noinline] def readP (i : Nat) : Nat := (mkP i).1 + (mkP (i + 1)).2

@[noinline] def twoUses (n : Nat) : Array (Nat × Nat) × Array (Nat × Nat) := Id.run do
  let mut a := Array.mkEmpty n
  let mut b := Array.mkEmpty n
  for i in [0:n] do
    let r := mkP i
    a := a.push r
    let q := if i % 2 == 0 then r else (i, i)
    b := b.push q
  return (a, b)

unsafe def main (args : List String) : IO Unit := do
  match args with
  | [mode, k] =>
    let n := k.toNat!
    if mode == "store" then
      let out := storeAll ⟨n, 1, 0⟩ n
      IO.println s!"{out.size} {tallyScore [(1, 2), (3, 4)]} {out.foldl (fun a b => a + b.hits) 0}"
    else
      let (a, b) := twoUses n
      IO.println s!"{a.size} {b.size} {readP 3}"
  | _ =>
    let b0 : Best := ⟨7, 1, 0⟩
    let out := storeAll b0 1000
    IO.println s!"store {out[0]!.key} {out[999]!.key} {out[999]!.score} {tallyScore [(1, 2)]} same={ptrAddrUnsafe out[0]! == ptrAddrUnsafe b0}"
    let (a, b) := twoUses 3
    IO.println s!"twoUses {a} {b} {readP 1} same={ptrAddrUnsafe a[0]! == ptrAddrUnsafe b[0]!}"
