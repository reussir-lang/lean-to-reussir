/-! Runtime test (`LEAN_NUM_THREADS=0`, `NAME.pipe`): natively no task
manager is created (`atoi`, 0): tasks run at once, where they are created,
and `IO.Promise.new` is Lean's internal panic. -/
def main : IO Unit := do
  let t ← IO.asTask (do IO.println "task runs at once"; return 1)
  IO.println "main after asTask"
  let d ← IO.mapTask (fun r => do IO.println s!"dependent of {repr (r.toOption)}"; return 2) t
  IO.println s!"main after mapTask: {repr (← IO.wait d).toOption}"
  let s := Task.spawn fun _ => dbgTrace "pure task runs at once" fun _ => 3
  IO.println s!"spawned: {s.get}"
  let _ ← IO.Promise.new (α := Nat)
  IO.println "after Promise.new"
