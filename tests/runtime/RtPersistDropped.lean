/-! Runtime test: the walk of a closed term for its tasks must not run a task the
program dropped during the walk. The closed term (one unsafe initializer) holds a
reference and a task t0; t0 is created first, so the lone worker runs it first, and it
replaces the reference's task T1 (created after t0) with T2. Natively T1 is dropped
while still queued and never runs; T2 runs when the walk reaches the reference. One
worker thread, busy with another task (`RtPersistDropped.pipe`), so the traces
(stderr) come in a fixed order. From review round 7, area L, round 4 (RV7L-07). -/
unsafe def mkU (_ : Unit) : IO.Ref (Task Nat) × Task Nat := unsafeBaseIO do
  let k ← IO.mkRef 0
  let r ← IO.mkRef (Task.pure 0)
  let t0 := Task.spawn fun _ => dbgTrace "t0 writes" fun _ =>
    unsafeBaseIO (do r.set (Task.spawn fun _ => dbgTrace "T2 (written by t0)" fun _ => 2); pure 0)
  -- T1 captures t0 (without forcing it), so it is created after t0
  r.set (Task.spawn fun _ => dbgTrace "T1 (replaced before it starts)" fun _ =>
    if unsafeBaseIO k.get == 12345 then t0.get else 1)
  pure (r, t0)
@[implemented_by mkU] opaque mk (u : Unit) : IO.Ref (Task Nat) × Task Nat

def main : IO Unit := do
  let busy ← IO.asTask (do IO.sleep 50; return 1)
  IO.eprintln "main"
  let (r, t0) := mk ()
  IO.eprintln s!"walked {t0.get}"
  IO.eprintln s!"value {(← r.get).get}"
  let _ ← IO.wait busy
  IO.eprintln "end"
