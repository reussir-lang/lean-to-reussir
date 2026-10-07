/-! Runtime test (review RS15-01 of switch step 15): a dedicated task whose
result the program dropped. Natively `run_task` frees its value on the
task's own thread (the `m_deleted` branch), before that thread's
finalizers drop its current streams. The value holds the last reference to
a promise, whose `sync` dependent prints: natively through the task
thread's stdout, which the task set to `tag` (a line on stderr). lean2rr
closed the task's stream context inside the job, before the value's free,
so the dependent printed to the process's stdout; the runtime's
`task_end` now closes it, after the job returned. -/
def tag : IO.FS.Stream := {
  flush := pure ()
  read := fun _ => pure .empty
  write := fun _ => pure ()
  getLine := pure ""
  putStr := fun s => IO.eprint s!"[task stdout] {s}"
  isTty := pure false }

def main : IO Unit := do
  let p : IO.Promise Unit ← IO.Promise.new
  let _ ← IO.mapTask (sync := true) (fun _ => IO.println "dependent runs") p.result?
  let _ ← IO.asTask (prio := .dedicated) (do
    let _ ← IO.setStdout tag
    pure p)
  IO.sleep 200
  IO.println "main ends"
