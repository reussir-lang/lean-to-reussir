/-! Runtime test (with one native worker thread, `NAME.pipe`): a dropped
`sync` dependent of a promise is deleted when the promise is resolved, and
does not take the worker's place: the tasks queued after it start only when
the worker is free. -/
def main : IO Unit := do
  let a ← IO.asTask (do IO.sleep 100; IO.println "A done")
  IO.sleep 20
  let p ← IO.Promise.new (α := Nat)
  let r ← IO.mkRef (p.result?.map (sync := true) fun x => dbgTrace "dropped dependent runs" fun _ => x)
  r.set (Task.pure none)
  p.resolve 1
  let b ← IO.asTask (do IO.sleep 50; IO.println "B done")
  let c ← IO.asTask (do IO.sleep 50; IO.println "C done")
  IO.sleep 100
  IO.println "main at 120"
  let _ ← IO.wait a
  let _ ← IO.wait b
  let _ ← IO.wait c
