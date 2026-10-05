/-! Runtime test (lean-runtime's case `refs/get_during_modify`): `r.modify f` is
`take`, then a store back (`ST.Prim.Ref.modifyUnsafe`), so `r` is empty while `f`
runs; here `f` waits for a dedicated task, and `main` reads `r` meanwhile. Natively
the reference is shared with a task and `lean_st_ref_get` spins while it is empty:
the read waits for `modify`'s store and returns its value. lean2rr's `take` leaves
the placeholder in the reference; in a program that creates tasks its `get` waits
while `modify` holds the reference (Lean 4.35's rule, lean-runtime's glue item 7:
`leanrt::refs`), so it reads modify's value too. -/

def slowValue (slow : Task (Except IO.Error Nat)) : Nat :=
  match slow.get with
  | .ok n => n
  | .error _ => 0

def main (args : List String) : IO Unit := do
  let readMs := args[0]!.toNat!
  let slowMs := args[1]!.toNat!
  let r ← IO.mkRef (0 : Nat)
  let slow ← IO.asTask (prio := .dedicated) do
    IO.sleep slowMs.toUInt32
    return 1
  let t ← IO.asTask (prio := .dedicated) do
    r.modify fun v => v + slowValue slow
  IO.sleep readMs.toUInt32
  let t0 ← IO.monoMsNow
  let v ← r.get
  let t1 ← IO.monoMsNow
  let how := if t1 - t0 ≥ (slowMs - readMs) / 2 then "after modify's set" else "at once"
  IO.println s!"get during modify: {v}, {how}"
  let _ ← IO.wait t
  IO.println s!"after modify: {← r.get}"
