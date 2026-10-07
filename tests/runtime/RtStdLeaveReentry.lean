/-! Runtime test (hunt HST-02, of the per-thread standard streams): at the
end of `main` its current streams are dropped (natively its thread's
finalizers, the last registered first: here stdout, then stderr). The drop
of the stderr stream drops the last reference to an unresolved promise
(the stream's `isTty` holds it), whose `sync` dependent then runs and
prints to stdout, whose cell was already dropped: natively a new
thread-local stdout, the process's, is made and never finalized, and both
lines are printed. lean2rr's leave of `main`'s streams asserted that the
cell stayed empty and aborted the program, with no output; it now leaves
such a cell as it is. -/
def main : IO Unit := do
  let p : IO.Promise Unit ← IO.Promise.new
  let _ ← IO.mapTask (sync := true) (fun _ => IO.println "dependent runs at main's end") p.result?
  let s : IO.FS.Stream := {
    flush := pure ()
    read := fun _ => pure {}
    write := fun _ => pure ()
    getLine := pure ""
    putStr := fun _ => pure ()
    isTty := p.isResolved }
  let _ ← IO.setStderr s
  IO.println "main ends"
