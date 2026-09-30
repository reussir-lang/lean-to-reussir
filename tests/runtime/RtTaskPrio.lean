/-! Runtime test (with one native worker thread, `NAME.pipe`): the tasks
still queued when `main` returns start in the order of Lean's task manager:
the task the worker already started first, then by priority, highest first
(`Task.Priority.max` before the default). -/
def main : IO Unit := do
  let _ ← IO.asTask (do IO.sleep 300; IO.println "blocker")
  IO.sleep 50
  let _ ← IO.asTask (IO.println "default")
  let _ ← IO.asTask (prio := .max) (IO.println "max")
  let _ ← IO.asTask (prio := 3) (IO.println "prio 3")
  let _ ← IO.asTask (IO.println "default 2")
