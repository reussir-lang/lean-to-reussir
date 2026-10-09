/-! Runtime test (with one native worker thread, `NAME.pipe`, which also
prints the file after the exit): `Runtime.forget` never releases its
argument, as native `lean_runtime_forget` (`Init/System/IO.lean`: the
value and every object it reaches are never freed). A forgotten
unresolved promise stays unresolved; a forgotten pure task that waits for
the busy worker still runs; a forgotten file handle stays open, so its
buffered bytes are not in the file yet, and are written at the exit (hunt
HTSK2-01). Before the fix lean2rr released the argument: the promise was
resolved with `none`, the task was deleted before it started, and the
handle was closed (its bytes written at once). The primitive takes the
value boxed, as natively: a `[value]` record (the unit, a structure of one
field) cannot cross the FFI boundary, so a generic texture rejected
`Runtime.forget ()`. -/
structure Wrap where
  s : String

def stateStr : IO.TaskState → String
  | .waiting => "waiting" | .running => "running" | .finished => "finished"

def main (args : List String) : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  let r := p.result?
  Runtime.forget p
  IO.println s!"promise after forget: {stateStr (← IO.getTaskState r)}"
  -- The one worker is busy for 300 ms; `t` reads `args`, so it is no
  -- closed term: it is queued behind the IO task.
  let io ← IO.asTask (do IO.sleep 300; IO.println "io task done")
  IO.sleep 50
  let t := Task.spawn fun _ => dbgTrace "forgotten pure task ran" fun _ => args.length + 42
  Runtime.forget t
  let _ ← IO.wait io
  IO.sleep 200
  let h ← IO.FS.Handle.mk "forget-h.txt" .write
  h.putStr "buffered bytes"
  Runtime.forget h
  IO.println s!"file after forget: {repr (← IO.FS.readFile "forget-h.txt")}"
  -- Values that are no heap object here: boxed for the call.
  Runtime.forget ()
  Runtime.forget (Wrap.mk s!"w{args.length}")
  Runtime.forget (args.length.toFloat + 0.5)
  Runtime.forget (args.length.toUInt64 + ((1 : UInt64) <<< 63))
  IO.println "main done"
