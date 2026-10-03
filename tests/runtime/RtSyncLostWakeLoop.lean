import Std.Sync
/-! Runtime test: a reference holding promises (a structure in an
`Option`, a list, an array) is cleared while `main` holds a mutex; a
promise's `sync` dependent sets a flag and notifies a condition variable;
then `main` waits in the usual loop, reading the flag before each wait.
Natively the dependent ran during the set, so the loop does not wait:
here too (the reference's old value is freed by the runtime, which runs
the dependents when that free ends), with or without Reussir patch 0040. -/

structure Pending where
  id : Nat
  p : IO.Promise Unit

def mkDep (p : IO.Promise Unit) (act : IO Unit) : BaseIO Unit := do
  let _ ← BaseIO.mapTask (sync := true) (t := p.result?) fun _ =>
    act.catchExceptions (fun _ => pure ())
  pure ()

def main : IO Unit := do
  for mode in ["option", "list", "array"] do
    let flag ← IO.mkRef false
    let m ← Std.BaseMutex.new
    let cv ← Std.Condvar.new
    let act : IO Unit := do flag.set true; cv.notifyAll
    if mode == "option" then
      let r ← IO.mkRef (none : Option Pending)
      let p ← IO.Promise.new
      mkDep p act
      r.set (some { id := 1, p })
      m.lock
      r.set none
    else if mode == "list" then
      let r ← IO.mkRef ([] : List (IO.Promise Unit))
      for i in [0:3] do
        let p ← IO.Promise.new
        if i == 0 then mkDep p act
        r.modify (p :: ·)
      m.lock
      r.set []
    else
      let r ← IO.mkRef (#[] : Array (IO.Promise Unit))
      let p ← IO.Promise.new
      mkDep p act
      r.modify (·.push p)
      m.lock
      r.set #[]
    while !(← flag.get) do cv.wait m
    m.unlock
    IO.println s!"{mode}: woken"
