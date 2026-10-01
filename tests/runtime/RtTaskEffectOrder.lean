import Std.Sync.Mutex
import Std.Async
/-! Runtime test: what natively runs on other threads while `main`
computes comes before `main`'s later output: a task woken by a promise, a
lock handed over, a condition variable's waiter, an `Async` timer's
continuation, a task blocked on a timer, a task in `IO.sleep`; a task whose
sleep is over before `IO.Process.exit`. (`main` computes 100 ms; the others
are woken or due well before.) -/
open Std Std.Async

def busy (ms : Nat) : IO Unit := do
  let start ← IO.monoMsNow
  while (← IO.monoMsNow) - start < ms do
    pure ()

def main : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  let t ← IO.asTask do
    let v ← IO.wait p.result!
    IO.println s!"task got {v}"
  IO.sleep 20
  p.resolve 5
  busy 100
  IO.println "main after busy (promise)"
  let _ ← IO.wait t
  let m ← Mutex.new (0 : Nat)
  let t ← m.atomically do
    let t ← IO.asTask (m.atomically (do IO.println "task got the lock"))
    IO.sleep 20
    return t
  busy 100
  IO.println "main after busy (lock)"
  let _ ← IO.wait t
  let m ← Mutex.new false
  let cv ← Condvar.new
  let t ← IO.asTask do
    m.atomicallyOnce cv get (pure ())
    IO.println "waiter woke"
  IO.sleep 20
  m.atomically (set true)
  cv.notifyAll
  busy 100
  IO.println "main after busy (condition variable)"
  let _ ← IO.wait t
  let t ← (do sleep 20; IO.println "async timer continuation" : Async Unit).toIO
  busy 100
  IO.println "main after busy (timer)"
  t.block
  let t2 ← IO.asTask (do (sleep 20 : Async Unit).block; IO.println "task blocked on a timer")
  IO.sleep 5
  busy 100
  IO.println "main after busy (blocked on a timer)"
  let _ ← IO.wait t2
  let t3 ← IO.asTask (do IO.sleep 20; IO.println "task in IO.sleep")
  IO.sleep 5
  busy 100
  IO.println "main after busy (sleep)"
  let _ ← IO.wait t3
  let _t ← IO.asTask (do IO.sleep 20; IO.println "task before exit")
  IO.sleep 5
  busy 100
  IO.Process.exit 0
