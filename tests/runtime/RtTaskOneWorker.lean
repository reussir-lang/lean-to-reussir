/-! Runtime test (with one native worker thread, `NAME.pipe`): tasks created
back to back and left for the exit start in priority order: the worker
(a new thread, or an idle one woken up) picks its first task only after
`main` has queued them all. With time between the first task and the next
ones, the worker has started the first one by then (see RtTaskPrio). -/
def pr (s : String) : IO Unit := do IO.println s; (← IO.getStdout).flush

def main (args : List String) : IO Unit := do
  if args.headD "" == "warm" then
    let w ← IO.asTask (pr "warm-up task")
    let _ ← IO.wait w
    IO.sleep 20
  let _ ← IO.asTask (pr "A default")
  let _ ← IO.asTask (prio := .max) (pr "B max")
  let _ ← IO.asTask (prio := .max) (pr "C max")
  let _ ← IO.asTask (pr "D default")
  let _ ← IO.asTask (prio := 4) (pr "E prio 4")
