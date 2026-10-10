/-! Runtime test: what `Runtime.markPersistent` marked stays persistent, and
a later mark does not look into it again, as natively
(`lean_mark_persistent` skips an object whose count is 0 already). A
reference is marked while it holds `none`, then set to an unfinished task;
a thunk is marked before it is forced, then forced (its value is an
unfinished task). Both are then marked again inside a structure. Natively
the second mark does not wait for the two tasks: `main` sees both
unfinished. lean2rr skipped the first walk while no task was unfinished,
and kept no mark between walks, so the second walk waited for both tasks
(review RV-01 of HTSK2-02). -/
structure Pack where
  ref : IO.Ref (Option (Task (Except IO.Error Nat)))
  lazy : Thunk (Task Nat)
  name : String

unsafe def main (args : List String) : IO Unit := do
  let r ← IO.mkRef (none : Option (Task (Except IO.Error Nat)))
  let r ← Runtime.markPersistent r
  let th : Thunk (Task Nat) := Thunk.mk fun _ =>
    Task.spawn (prio := .dedicated) fun _ =>
      dbgSleep 300 fun _ => dbgTrace "thunk's task: done" fun _ => args.length + 2
  let th ← Runtime.markPersistent th
  let t ← IO.asTask (prio := .dedicated) do
    IO.sleep 200
    IO.println "ref's task: done"
    pure args.length
  r.set (some t)
  let tt := th.get
  let p ← Runtime.markPersistent ({ ref := r, lazy := th, name := "pack" } : Pack)
  IO.println s!"main: marked {p.name} again"
  IO.println s!"main: finished {← IO.hasFinished t} {← IO.hasFinished tt}"
  let _ ← IO.wait t
  IO.println s!"main: {tt.get}"
