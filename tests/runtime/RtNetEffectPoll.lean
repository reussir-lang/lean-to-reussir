import Std.Internal.UV
import Std.Net.Addr
open Std.Internal.UV Std.Net

/-! Runtime test: output while a socket operation is pending. The event
loop's descriptors are polled at effect points (outputs), at most every
50 µs rather than once per output: a long output loop with an accept
pending prints as natively, and a connection made by a child process
while `main` prints in a loop is accepted during the loop
(`RtNetEffectPoll.pipe` drops the loops' lines). -/

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
  let accepted ← IO.mkRef false
  let p ← s.accept
  let _ ← BaseIO.mapTask (sync := true) (t := p.result?) fun _ => accepted.set true
  let child ← IO.Process.spawn { cmd := "bash", args := #["-c", s!"exec 3<>/dev/tcp/127.0.0.1/{port}; sleep 0.3"] }
  -- A deadline, not an iteration count: on a loaded machine native Lean
  -- printed 100 million lines before the child had connected.
  let deadline := (← IO.monoMsNow) + 60000
  let mut i := 0
  while !(← accepted.get) && (← IO.monoMsNow) < deadline do
    out.putStrLn s!"waiting {i}"
    i := i + 1
  IO.println s!"accepted during the loop: {← accepted.get}"
  let _ ← child.wait
  IO.println "done"
