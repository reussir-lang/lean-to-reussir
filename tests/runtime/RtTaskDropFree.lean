import Std.Sync.Mutex
/-! Runtime test: promises dropped inside the free of a container (an array
of them, released through a reference), with `sync` dependents: natively
the release resolves each promise with `none` in Lean's order (the last
element first) and runs its dependents at once on the dropping thread,
before `main`'s next line; one dependent sleeps, one waits for a lock a
task holds. -/
def main : IO Unit := do
  let ps ← (Array.range 3).mapM fun _ => IO.Promise.new (α := Nat)
  let mut deps := #[]
  for h : i in [0:ps.size] do
    deps := deps.push (← IO.mapTask (sync := true) (fun r => IO.println s!"dep {i}: {r.isSome}") ps[i].result?)
  let r ← IO.mkRef (some ps)
  r.set none
  IO.println "after the first drop"
  let qs ← (Array.range 2).mapM fun _ => IO.Promise.new (α := Nat)
  let m ← Std.BaseMutex.new
  let locked ← IO.Promise.new (α := Unit)
  let holder ← IO.asTask (do m.lock; locked.resolve (); IO.sleep 20; m.unlock)
  IO.wait locked.result!
  let mut deps2 := #[]
  for h : i in [0:qs.size] do
    deps2 := deps2.push (← IO.mapTask (sync := true) (fun r => do
      if i == 0 then
        IO.sleep 10
        IO.println s!"slept dep {i}: {r.isSome}"
      else
        m.lock
        IO.println s!"waiting dep {i}: {r.isSome}"
        m.unlock) qs[i].result?)
  let r2 ← IO.mkRef (some qs)
  r2.set none
  IO.println "after the second drop"
  for d in deps ++ deps2 do
    let _ ← IO.wait d
  let _ ← IO.wait holder
  IO.println "done"
