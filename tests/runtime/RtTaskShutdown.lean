/-! Runtime test (with one native worker thread, `NAME.pipe`): when `main`
returns, Lean sets its shutdown flag and runs the queued tasks;
`IO.checkCanceled` is true in every task that could only start after that:
dependents of a task still pending then (`sync` or not), tasks created by a
task running after it, and bind continuations created then. -/
def main : IO Unit := do
  let t ← IO.asTask (do IO.sleep 50; IO.println "source"; return 1)
  let _ ← IO.mapTask (sync := true) (fun _ => do IO.println s!"sync dependent {← IO.checkCanceled}") t
  let _ ← IO.mapTask (fun _ => do IO.println s!"dependent {← IO.checkCanceled}") t
  let _ ← IO.bindTask t (fun _ => IO.asTask (do IO.println s!"continuation {← IO.checkCanceled}"; return 2))
  let _ ← IO.asTask (do
    IO.sleep 20
    let _ ← IO.asTask (do IO.println s!"child {← IO.checkCanceled}")
    IO.println "parent end")
  IO.println "main end"
