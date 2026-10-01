/-! Runtime test (with one native worker thread, `NAME.pipe`): a pure task
(`Task.spawn`, `Task.map`, `Task.bind`) that the program drops before it has
started never runs: Lean deletes it. Here the single worker is busy with a
blocker, so the tasks below are all still queued when they are dropped.
An IO task the program drops still runs, and so does a pure task that a
pending IO task keeps alive. -/
def work (tag : String) (n : Nat) : Nat := dbgTrace s!"{tag} runs" fun _ => n + 1

def main (args : List String) : IO Unit := do
  let n := args.length
  let blocker ← IO.asTask (do IO.sleep 100; IO.println "blocker"; return 1)
  IO.sleep 20
  let r ← IO.mkRef (Task.spawn fun _ => work "dropped spawn" n)
  r.set (Task.pure 0)
  let r2 ← IO.mkRef (blocker.map fun x => work "dropped map" (x.toOption.getD 0))
  r2.set (Task.pure 0)
  let r3 ← IO.mkRef (blocker.map (sync := true) fun x => work "dropped sync map" (x.toOption.getD 0))
  r3.set (Task.pure 0)
  let r4 ← IO.mkRef (blocker.bind fun x => Task.spawn fun _ => work "dropped bind" (x.toOption.getD 0))
  r4.set (Task.pure 0)
  -- a dropped task and a dropped dependent of it (which holds it)
  let s := Task.spawn fun _ => work "dropped source" n
  let r5 ← IO.mkRef (some (s, s.map (work "dropped map of source")))
  r5.set none
  let r6 ← IO.mkRef (← IO.asTask (do IO.println "dropped io task runs"; return 2))
  r6.set (Task.pure (.ok 0))
  let kept := Task.spawn fun _ => work "kept spawn" n
  let _ ← IO.asTask (do if n > 100 then IO.println s!"{kept.get}")
  let _ ← IO.wait blocker
