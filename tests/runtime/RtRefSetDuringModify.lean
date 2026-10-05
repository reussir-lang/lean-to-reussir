/-! Runtime test (lean-runtime's case `refs/set_during_modify`, LB-01): while
`modify`'s function waits for a task, `main` sets the reference, then reads it.
Lean 4.35's rule (lean-runtime's): `set` waits for `modify`'s store, so `main`'s
value is not lost and `r` ends 100 (`RtRefSetDuringModify.l2r.out`). Native
4.34.0 stores into the empty slot at once and `modify`'s store overwrites it, so
`r` ends 1 (`RtRefSetDuringModify.native.out`; LB-01, not reproduced: lean2rr's
`set` waits in a program that creates tasks, `leanrt::refs`). -/

def slowValue (slow : Task (Except IO.Error Nat)) : Nat :=
  match slow.get with
  | .ok n => n
  | .error _ => 0

def main (args : List String) : IO Unit := do
  let setMs := args[0]!.toNat!
  let slowMs := args[1]!.toNat!
  let r ← IO.mkRef (0 : Nat)
  let slow ← IO.asTask (prio := .dedicated) do
    IO.sleep slowMs.toUInt32
    return 1
  let t ← IO.asTask (prio := .dedicated) do
    r.modify fun v => v + slowValue slow
  IO.sleep setMs.toUInt32
  r.set 100
  let t0 ← IO.monoMsNow
  let v ← r.get
  let t1 ← IO.monoMsNow
  let how := if t1 - t0 ≥ (slowMs - setMs) / 2 then "after modify's set" else "at once"
  IO.println s!"get after main's set: {v}, {how}"
  let _ ← IO.wait t
  IO.println s!"after modify: {← r.get}"
