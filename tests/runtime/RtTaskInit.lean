/-! Runtime test: during module initialization (`initialize`) there is no
task manager, so `IO.asTask` runs the action at once; in `main` tasks are
deferred. -/

initialize do
  let t ← IO.asTask (do IO.println "init task runs"; return 7)
  IO.println "init: after asTask"
  match ← IO.wait t with
  | .ok v => IO.println s!"init: got {v}"
  | .error _ => pure ()

def main : IO Unit := do
  let t ← IO.asTask (do IO.sleep 100; IO.println "main task runs"; return 8)
  IO.println "main: after asTask"
  match ← IO.wait t with
  | .ok v => IO.println s!"main: got {v}"
  | .error _ => pure ()
