/-! Runtime test (lean-runtime's case `refs/swap_during_modify`, LB-18): while
`modify`'s function waits for a task, `main` swaps the reference. Lean 4.35's rule
(lean-runtime's): `swap` waits for `modify`'s store and returns it, and `r` ends
100 (`RtRefSwapDuringModify.l2r.out`). Native 4.34.0's `swap` returns its own
argument at once, one object with two owners, and `r` ends 1
(`RtRefSwapDuringModify.native.out`; LB-18, not reproduced: lean2rr's `swap`
waits in a program that creates tasks, `leanrt::refs`). -/

def slowValue (slow : Task (Except IO.Error Nat)) : Nat :=
  match slow.get with
  | .ok n => n
  | .error _ => 0

def main (args : List String) : IO Unit := do
  let swapMs := args[0]!.toNat!
  let slowMs := args[1]!.toNat!
  let r ← IO.mkRef (0 : Nat)
  let slow ← IO.asTask (prio := .dedicated) do
    IO.sleep slowMs.toUInt32
    return 1
  let t ← IO.asTask (prio := .dedicated) do
    r.modify fun v => v + slowValue slow
  IO.sleep swapMs.toUInt32
  let t0 ← IO.monoMsNow
  let old ← r.swap 100
  let t1 ← IO.monoMsNow
  let how := if t1 - t0 ≥ (slowMs - swapMs) / 2 then "after modify's set" else "at once"
  IO.println s!"swap during modify returned: {old}, {how}"
  let _ ← IO.wait t
  IO.println s!"after modify: {← r.get}"
