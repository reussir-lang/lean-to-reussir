import Std.Internal.UV
open Std.Internal.UV
/-! Runtime test (hunt HST-01, of the per-thread standard streams):
natively libuv's loop is one thread for the whole program, so the current
stdout that one callback's `sync` dependent sets (and does not restore) is
still the loop thread's when a later callback's `sync` dependent prints.
Between the two callbacks a pool task blocks, so the next loop context
starts on another id. lean2rr kept a context's streams by its id, so the
second callback's dependent printed to the process's stdout ("d2 (buffer)"
first, and the buffer held only d1's line); the event loop's contexts now
share one record. -/
def main : IO Unit := do
  let r ← IO.mkRef ""
  let s : IO.FS.Stream := {
    flush := pure ()
    read := fun _ => pure {}
    write := fun _ => pure ()
    getLine := pure ""
    putStr := fun x => r.modify (· ++ x)
    isTty := pure false }
  -- the first callback's sync dependent sets the loop thread's stdout
  let t1 ← Timer.mk 30 false
  let p1 ← t1.next
  let d1 ← IO.mapTask (sync := true) (fun _ => do
    let _ ← IO.setStdout s
    IO.println "d1 (buffer)") p1.result?
  let _ ← IO.wait d1
  -- a pool task blocks meanwhile
  let gate : IO.Promise Unit ← IO.Promise.new
  let blocker ← IO.asTask (do let _ ← IO.wait gate.result?; pure ())
  IO.sleep 30
  -- the second callback's sync dependent prints (natively into the buffer)
  let t2 ← Timer.mk 30 false
  let p2 ← t2.next
  let d2 ← IO.mapTask (sync := true) (fun _ => IO.println "d2 (buffer)") p2.result?
  let _ ← IO.wait d2
  gate.resolve ()
  let _ ← IO.wait blocker
  IO.println s!"buffer: {(← r.get).trimAscii.copy.quote}"
