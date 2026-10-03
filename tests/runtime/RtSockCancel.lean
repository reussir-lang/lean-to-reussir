import Std.Internal.UV
import Std.Net.Addr
open Std.Internal.UV Std.Net

/-! Runtime test: `cancelAccept` and `cancelRecv` drop the promise of the
pending operation unresolved. Natively it is released in the call, on the
calling thread, so its `sync` dependents have run when the call returns
(here too: the glue drops it once the primitive has returned). The read
is on a connection from a child process; also a `waitReadable` and a
UDP read. -/

def listener : IO TCP.Socket := do
  let s ← TCP.Socket.new
  s.bind (.v4 { addr := IPv4Addr.ofParts 127 0 0 1, port := 0 })
  s.listen 16
  return s

def main : IO Unit := do
  let log ← IO.mkRef (#[] : Array String)
  let s ← listener
  do
    let p ← s.accept
    let _ ← BaseIO.mapTask (sync := true) (t := p.result?) fun r =>
      log.modify (·.push s!"accept {if r.isSome then "resolved" else "dropped"}")
  s.cancelAccept
  IO.println s!"right after cancelAccept: {← log.get}"
  let s2 ← listener
  let port := match ← s2.getSockName with
    | .v4 a => a.port
    | .v6 a => a.port
  let child ← IO.Process.spawn { cmd := "bash", args := #["-c", s!"exec 3<>/dev/tcp/127.0.0.1/{port}; sleep 1"] }
  let c ← IO.ofExcept (← IO.wait (← s2.accept).result!)
  do
    let p ← c.recv? 100
    let _ ← BaseIO.mapTask (sync := true) (t := p.result?) fun r =>
      log.modify (·.push s!"recv {if r.isSome then "resolved" else "dropped"}")
  c.cancelRecv
  IO.println s!"right after cancelRecv: {← log.get}"
  do
    let p ← c.waitReadable
    let _ ← BaseIO.mapTask (sync := true) (t := p.result?) fun r =>
      log.modify (·.push s!"waitReadable {if r.isSome then "resolved" else "dropped"}")
  c.cancelRecv
  IO.println s!"right after cancelling waitReadable: {← log.get}"
  let _ ← child.wait
  -- a UDP read on a bound socket
  let u ← UDP.Socket.new
  u.bind (.v4 { addr := IPv4Addr.ofParts 127 0 0 1, port := 0 })
  do
    let p ← u.recv 100
    let _ ← BaseIO.mapTask (sync := true) (t := p.result?) fun r =>
      log.modify (·.push s!"udp recv {if r.isSome then "resolved" else "dropped"}")
  u.cancelRecv
  IO.println s!"right after UDP cancelRecv: {← log.get}"
