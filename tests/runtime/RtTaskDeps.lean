/-! Runtime test: tasks still queued when `main` returns start in the order
Lean's task manager enqueues them: the dependents of a task are enqueued
when it finishes, the one registered last first, and an `IO.bindTask` task
that has run `f` waits for the task it continues as (enqueued at its end). -/

@[noinline] def hn (x : Nat) : Nat := x

def main : IO Unit := do
  let t ← IO.asTask (do IO.sleep 10; IO.println "base"; return hn 1)
  let _ ← IO.mapTask (fun _ => IO.println "first registered") t
  let _ ← IO.bindTask t (fun r => do IO.println s!"bind {r.toOption}"; IO.asTask (IO.println "bind inner"))
  IO.println "main returns"
