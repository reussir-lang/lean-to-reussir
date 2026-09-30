/-! Runtime test: tasks still pending when `main` fails run before the
uncaught exception is reported (Lean's task manager finishes them first),
in creation order when they do not race; the exit code is 1. -/

def main : IO Unit := do
  let _ ← IO.asTask (do IO.sleep 100; IO.println "first pending task")
  let t ← IO.asTask (do IO.sleep 300; IO.println "second pending task")
  let _ ← IO.mapTask (fun _ => IO.println "after the second") t
  IO.println "main fails"
  throw (IO.userError "main failed")
