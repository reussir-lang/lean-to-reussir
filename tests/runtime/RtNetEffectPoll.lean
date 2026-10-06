import Std.Internal.UV
import Std.Net.Addr
open Std.Internal.UV Std.Net

/-! Runtime test: output while a socket operation is pending. The event
loop's descriptors are polled at effect points (outputs), at most every
50 µs rather than once per output: a long output loop with an accept
pending prints as natively, and a connection made by a child process
while `main` prints in a loop is accepted during the loop
(`RtNetEffectPoll.pipe` drops the loops' lines).

The second loop asks whether the accept's `sync` dependent has finished:
a task that has finished stays finished. The loop reads no `IO.Ref` that
the dependent writes. In native Lean 4.34.0, a `get` that runs at the same
time as the dependent's `set` can put the old value back (LB-01). A loop
that waits for such a flag then misses the accept and runs to its
deadline, which made this test fail natively now and then. -/

def listener : IO TCP.Socket := do
  let s ← TCP.Socket.new
  s.bind (.v4 { addr := IPv4Addr.ofParts 127 0 0 1, port := 0 })
  s.listen 16
  return s

def main : IO Unit := do
  let out ← IO.getStdout
  let s1 ← listener
  let _p1 ← s1.accept
  for j in [0:200000] do
    out.putStrLn s!"line {j}"
  s1.cancelAccept
  let s ← listener
  let port := match ← s.getSockName with
    | .v4 a => a.port
    | .v6 a => a.port
  let p ← s.accept
  -- Runs when the accept completes: natively on the event loop's thread,
  -- in lean2rr at a point of `main`'s loop.
  let dep ← BaseIO.mapTask (sync := true) (t := p.result?) fun r =>
    pure (r matches some (.ok _))
  let child ← IO.Process.spawn { cmd := "bash", args := #["-c", s!"exec 3<>/dev/tcp/127.0.0.1/{port}; sleep 0.3"] }
  -- The deadline stops the loop if the connection never comes.
  let deadline := (← IO.monoMsNow) + 60000
  let mut i := 0
  let mut accepted ← IO.hasFinished dep
  while !accepted && (← IO.monoMsNow) < deadline do
    out.putStrLn s!"waiting {i}"
    i := i + 1
    accepted ← IO.hasFinished dep
  IO.println s!"accepted during the loop: {accepted}"
  -- The dependent's result, read only after it has finished.
  let conn ← if accepted then IO.wait dep else pure false
  IO.println s!"the dependent got a connection: {conn}"
  let _ ← child.wait
  IO.println "done"
