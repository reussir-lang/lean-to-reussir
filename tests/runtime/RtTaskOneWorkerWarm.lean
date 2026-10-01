/-! Runtime test (with one native worker thread, `NAME.pipe`): as
RtTaskOneWorker, with an idle worker thread already running, and a
dependent task released at exit among independent ones. -/
def pr (s : String) : IO Unit := do IO.println s; (← IO.getStdout).flush

def main : IO Unit := do
  let w ← IO.asTask (pr "warm-up task")
  let _ ← IO.wait w
  IO.sleep 20
  let a ← IO.asTask (do IO.sleep 50; pr "A sleeps"; return 1)
  let _ ← IO.mapTask (prio := .max) (fun _ => pr "dep max") a
  let _ ← IO.asTask (prio := 4) (pr "prio 4")
  let _ ← IO.asTask (pr "default")
  let _ ← IO.asTask (do
    IO.sleep 30
    let _ ← IO.asTask (pr "child default")
    let _ ← IO.asTask (prio := .max) (pr "child max")
    pr "parent end")
  let _ ← IO.asTask (prio := 1) (pr "sibling 1")
