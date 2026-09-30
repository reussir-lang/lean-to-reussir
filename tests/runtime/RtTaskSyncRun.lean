/-! Runtime test: a `sync := true` dependent runs as soon as the task it
waits for finishes, before `main`, waiting for that task, resumes (IO and
pure dependents, and a sync bind task's `f`); inside a task `IO.getTID`
differs from `main`'s, as a worker thread's does. -/
def main : IO Unit := do
  let r ← IO.mkRef 0
  let t0 ← IO.asTask (do IO.sleep 100; IO.println "t0"; return 1)
  let _ ← IO.mapTask (sync := true) (fun _ => r.set 42) t0
  let _ ← IO.mapTask (sync := true) (fun _ => IO.println "sync dep runs") t0
  let _ ← IO.bindTask (sync := true) t0 (fun _ => do IO.println "sync bind f"; return Task.pure (.ok 0))
  let _ ← IO.wait t0
  IO.println s!"main after wait: ref {← r.get}"
  let mt ← IO.getTID
  let t ← IO.asTask IO.getTID
  match ← IO.wait t with
  | .ok tt => IO.println s!"task tid is main's: {tt == mt}"
  | .error e => IO.println s!"error {e}"
