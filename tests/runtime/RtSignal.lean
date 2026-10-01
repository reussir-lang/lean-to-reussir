import Std.Async
/-! Runtime test: signal watchers (`Std.Internal.UV.Signal`, `Std.Async`'s
`Signal`): the promise of `next` is resolved with the signal's number when
the process gets it (sent here by `kill`); a repeating watcher, `stop`; an
unknown signal number fails with libuv's `EINVAL` when the watcher starts. -/
open Std.Internal.UV

def sendSelf (sig : String) : IO Unit := do
  let out ← IO.Process.output { cmd := "kill", args := #["-" ++ sig, toString (← IO.Process.getPID)] }
  if out.exitCode != 0 then IO.println s!"kill failed: {out.stderr}"

def main : IO Unit := do
  let s ← Signal.mk 10 false
  let p ← s.next
  IO.println s!"before: {← p.isResolved}"
  sendSelf "USR1"
  IO.println s!"got {← IO.wait p.result!}"
  let p2 ← s.next
  IO.println s!"one-shot again resolved: {← p2.isResolved}"
  let r ← Signal.mk 12 true
  for _ in [0:2] do
    let q ← r.next
    sendSelf "USR2"
    IO.println s!"repeating got {← IO.wait q.result!}"
  r.stop
  let bad ← Signal.mk 4 false
  try discard <| bad.next catch e => IO.println s!"unknown signal: {e}"
