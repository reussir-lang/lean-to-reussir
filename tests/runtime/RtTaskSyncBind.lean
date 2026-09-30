/-! Runtime test (with one native worker thread, `NAME.pipe`): a
`sync := true` bind task whose continuation was still pending waits for it
with its sync priority: when the continuation finishes, the bind task
finishes there and then, before the continuation's older dependents are
enqueued. -/
def say (s : String) : IO Unit := do IO.println s; (← IO.getStdout).flush

def main : IO Unit := do
  let b ← IO.asTask (do IO.sleep 300; say "blocker")
  IO.sleep 50
  let bt ← IO.bindTask (sync := true) b (fun _ => do
    let inner ← IO.asTask (say "inner")
    let _ ← IO.mapTask (fun _ => say "dep of inner") inner
    return inner)
  let _ ← IO.mapTask (fun _ => say "dep of bind") bt
