/-! Runtime test (with one native worker thread, `NAME.pipe`): native Lean
passes a task priority to its task manager as an `unsigned`
(`lean_unbox(prio)`): modulo 2^32, and 2^32-1 is `LEAN_SYNC_PRIO`, which
runs the task as soon as it is enqueued, on the enqueuing thread (an IO
task or `Task.spawn` at once, in `main`, a dependent as soon as its source
finishes), and 2^32+1 and 2^33+4 are the pool's priorities 1 and 4
(`NAME.native.out`). lean2rr passes the whole priority (lean-runtime's
LB-39): each of them is above 8, a dedicated task, which runs on a context
of its own and, at exit, before the pool's tasks (`NAME.l2r.out`). -/
def ex (x : Except IO.Error Nat) : Nat := x.toOption.getD 999

def stateStr : IO.TaskState → String
  | .waiting => "waiting" | .running => "running" | .finished => "finished"

@[noinline] def big (k : Nat) : Nat := k

def main (args : List String) : IO Unit := do
  let mt ← IO.getTID
  let t ← IO.asTask (prio := big 4294967295) (do
    IO.println "sync-priority task runs"
    return if (← IO.getTID) == mt then 1 else 0)
  IO.println s!"after asTask: {stateStr (← IO.getTaskState t)}, on main's thread {ex (← IO.wait t)}"
  let p := Task.spawn (prio := big 4294967295) fun _ => args.length + 41
  IO.println s!"spawn: {stateStr (← IO.getTaskState p)} {p.get}"
  let s ← IO.asTask (do IO.sleep 50; IO.println "source"; return 1)
  let _ ← IO.mapTask (prio := big 4294967295) (fun x => do IO.println s!"sync-priority dependent {ex x}"; return 2) s
  let _ ← IO.wait s
  IO.println "main after source"
  -- at exit: 2^32+1 is priority 1, 2^33+4 is 4
  let _ ← IO.asTask (prio := .max) (do IO.sleep 100; IO.println "first max")
  IO.sleep 20
  let _ ← IO.asTask (prio := 3) (IO.println "prio 3")
  let _ ← IO.asTask (prio := big 4294967297) (IO.println "prio 2^32+1")
  let _ ← IO.asTask (prio := big 8589934596) (IO.println "prio 2^33+4")
  let _ ← IO.asTask (prio := 2) (IO.println "prio 2")
  IO.println "main end"
