import Std.Sync
/-! Runtime test: right after a free that released promises (held by a
list or an array in an `IO.Ref`), `main` waits on a Std.Sync object (or a
promise) that a promise's `sync` dependent releases. Natively the
dependent has run during the free, so the wait does not block: the
condition variable was notified, the mutex unlocked, the promise
resolved. (Promises freed by Reussir's record glue are resolved, their
dependents walked, at the end of the free's drain, before such a wait
starts: lean-runtime's `run_deferred`, from Reussir's drain-end hook,
`task::hook_drained` and `drained`.) -/

-- Three promises in a list in a ref; the dependent of the last cell's
-- promise runs `act`.
def listRegistry (act : IO Unit) : IO (IO.Ref (List (IO.Promise Unit))) := do
  let reg ← IO.mkRef ([] : List (IO.Promise Unit))
  for i in [0:3] do
    let p ← IO.Promise.new
    reg.modify (p :: ·)
    let _ ← BaseIO.mapTask (sync := true) (t := p.result?) fun _ =>
      if i == 0 then act.catchExceptions (fun _ => pure ()) else pure ()
  return reg

def arrayRegistry (act : IO Unit) : IO (IO.Ref (Array (IO.Promise Unit))) := do
  let reg ← IO.mkRef (#[] : Array (IO.Promise Unit))
  let p ← IO.Promise.new
  reg.modify (·.push p)
  let _ ← BaseIO.mapTask (sync := true) (t := p.result?) fun _ =>
    act.catchExceptions (fun _ => pure ())
  return reg

def main : IO Unit := do
  -- a condition variable the dependent notifies
  let m ← Std.Mutex.new false
  let cv ← Std.Condvar.new
  let reg ← listRegistry (do m.atomically (set true); cv.notifyAll)
  reg.set []
  m.atomicallyOnce cv get (pure ())
  IO.println "condvar (list): woken"
  let m ← Std.Mutex.new false
  let cv ← Std.Condvar.new
  let reg ← arrayRegistry (do m.atomically (set true); cv.notifyAll)
  reg.set #[]
  m.atomicallyOnce cv get (pure ())
  IO.println "condvar (array): woken"
  -- a mutex `main` holds, which the dependent unlocks
  let bm ← Std.BaseMutex.new
  bm.lock
  let reg ← listRegistry bm.unlock
  reg.set []
  bm.lock
  IO.println "mutex (list): relocked"
  bm.unlock
  let bm ← Std.BaseMutex.new
  bm.lock
  let reg ← arrayRegistry bm.unlock
  reg.set #[]
  bm.lock
  IO.println "mutex (array): relocked"
  bm.unlock
  -- a promise the dependent resolves
  let q : IO.Promise Nat ← IO.Promise.new
  let reg ← listRegistry (q.resolve 5)
  reg.set []
  IO.println s!"promise (list): {← IO.wait q.result?}"
