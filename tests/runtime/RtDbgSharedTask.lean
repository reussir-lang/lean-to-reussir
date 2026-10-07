/-! Runtime test: `dbgTraceIfShared` on tasks (review HL-01). Natively a
task that `Task.spawn` made is multi-threaded (its count is negative), so
`lean_is_exclusive` is false and the check reports it even when one
reference holds it. lean2rr runs tasks on one thread and reads the task
cell's count, 1 there: not reported (plan §10, "Sharing is not
observable"; the expectation files RtDbgSharedTask.native.err and
.l2r.err). A pure task that one reference holds is reported by neither,
a spawned task that two references hold by both. -/
def main (args : List String) : IO Unit := do
  let n := args.length
  let t := Task.spawn fun _ => n + 1
  let t' := dbgTraceIfShared "spawned task, one reference" t
  IO.println t'.get
  let p := Task.pure (n + 2)
  let p' := dbgTraceIfShared "pure task, one reference" p
  IO.println p'.get
  let u := Task.spawn fun _ => n + 3
  let u2 := u
  let u' := dbgTraceIfShared "spawned task, two references" u
  IO.println (u'.get + u2.get)
