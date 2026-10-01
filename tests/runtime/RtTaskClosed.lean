/-! Runtime test: a pure task extracted as a closed term has finished once
the term has been evaluated (Lean's `lean_mark_persistent` waits for the
tasks it reaches), also inside a structure or a list. -/
def stateStr : IO.TaskState → String
  | .waiting => "waiting" | .running => "running" | .finished => "finished"

def main : IO Unit := do
  let busy ← IO.asTask (do IO.sleep 50; return 1)
  let p := Task.spawn fun _ => dbgTrace "closed task runs" fun _ => (8 : Nat)
  IO.println s!"state {stateStr (← IO.getTaskState p)}"
  let ps := [Task.spawn fun _ => (1 : Nat), Task.spawn fun _ => (2 : Nat)]
  let sts ← ps.mapM fun t => return stateStr (← IO.getTaskState t)
  IO.println s!"list {sts}"
  let q := (Task.spawn fun _ => "a", (3 : Nat))
  IO.println s!"pair {stateStr (← IO.getTaskState q.1)} {q.2}"
  let _ ← IO.wait busy
  IO.println s!"values {p.get} {ps.map Task.get} {q.1.get}"
