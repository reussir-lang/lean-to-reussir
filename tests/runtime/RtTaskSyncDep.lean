/-! Runtime test (with one native worker thread, `NAME.pipe`): a
`sync := true` dependent runs while Lean walks the finished task's
dependents, so a task it creates is enqueued before the older async
dependents; the walk goes from the newest dependent. -/
def main : IO Unit := do
  let b ← IO.asTask (do IO.sleep 300; IO.println "blocker")
  IO.sleep 50
  let _ ← IO.mapTask (fun _ => IO.println "async dep") b
  let _ ← IO.mapTask (sync := true) (fun _ => do
    let _ ← IO.asTask (IO.println "made by sync dep")) b
  let _ ← IO.mapTask (fun _ => IO.println "newest async dep") b
