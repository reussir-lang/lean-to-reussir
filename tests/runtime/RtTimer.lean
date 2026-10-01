import Std.Async
/-! Runtime test: timers (`Std.Async.sleep`, `Sleep`, `Interval`, and the
`Std.Internal.UV.Timer` state machine underneath). Timers fire in the order
of their deadlines, relative to each other, to `IO.sleep` and to tasks
(20 ms or more apart, so the native order is fixed); `Sleep.wait` twice
returns the same completion; `reset`, `stop`, `cancel`; an `Interval` ticks
at once, then every period. -/
open Std.Async

def stamp (log : IO.Ref (Array String)) (s : String) : IO Unit := log.modify (·.push s)

def main : IO Unit := do
  let r : Nat ← (do sleep 20; return 37 : Async Nat).block
  IO.println s!"slept {r}"
  -- background timers against main's sleep
  let log ← IO.mkRef #[]
  let _ ← (background (do sleep 60; stamp log "60 ms timer" : Async Unit)).toIO
  let _ ← (background (do sleep 20; stamp log "20 ms timer" : Async Unit)).toIO
  let _ ← IO.asTask (do IO.sleep 40; stamp log "40 ms task")
  IO.sleep 100
  stamp log "main after 100 ms"
  for l in ← log.get do IO.println l
  -- timers fire during a sleep and their continuations print in order
  let t1 ← (do sleep 30; IO.println "timer 30" : Async Unit).toIO
  let t2 ← (do sleep 10; IO.println "timer 10" : Async Unit).toIO
  IO.sleep 60
  IO.println "main after 60"
  t1.block; t2.block
  -- Sleep: wait twice, reset
  let x ← (do
      let s ← Sleep.mk 20
      s.wait
      s.wait
      s.reset
      s.wait
      return 1 : Async Nat).block
  IO.println s!"sleep twice {x}"
  -- Interval: the first tick at once
  let t0 ← IO.monoMsNow
  let n ← (do
      let i ← Interval.mk 15
      i.tick
      let t1 ← IO.monoMsNow
      i.tick
      i.tick
      let t2 ← IO.monoMsNow
      i.stop
      return (t1 - t0 < 10, t2 - t0 ≥ 25) : Async (Bool × Bool)).block
  IO.println s!"interval {n}"
  -- the raw timer: next after the timer fired, stop, cancel
  let tm ← Std.Internal.UV.Timer.mk 10 false
  let p ← tm.next
  IO.println s!"resolved before: {← p.isResolved}"
  IO.wait p.result!
  let p2 ← tm.next
  IO.println s!"same promise resolved after: {← p2.isResolved}"
  let tm2 ← Std.Internal.UV.Timer.mk 10 false
  let q ← tm2.next
  tm2.stop
  IO.sleep 30
  IO.println s!"stopped timer resolved: {← q.isResolved}"
  let q2 ← tm2.next
  IO.println s!"next after stop resolved: {← q2.isResolved}"
  let tm3 ← Std.Internal.UV.Timer.mk 10 false
  let c ← tm3.next
  tm3.cancel
  let c2 ← tm3.next
  IO.wait c2.result!
  IO.println s!"canceled promise resolved: {← c.isResolved}, restarted: {← c2.isResolved}"
  -- a repeating timer
  let rep ← Std.Internal.UV.Timer.mk 10 true
  let mut ticks := 0
  for _ in [0:3] do
    let p ← rep.next
    IO.wait p.result!
    ticks := ticks + 1
  rep.stop
  IO.println s!"repeating ticks {ticks}"
