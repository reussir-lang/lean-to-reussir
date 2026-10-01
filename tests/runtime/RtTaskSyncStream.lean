/-! Runtime test: a `sync := true` dependent runs on the thread that finished
its source, so it writes to the stream the source installed there. -/
def main : IO Unit := do
  let r ← IO.mkRef ""
  let s : IO.FS.Stream := {
    flush := pure ()
    read := fun _ => pure {}
    write := fun _ => pure ()
    getLine := pure ""
    putStr := fun x => r.modify (· ++ x)
    isTty := pure false }
  let src ← IO.asTask (do IO.sleep 20; let _ ← IO.setStdout s; IO.println "src (buffer)"; return 1)
  let d ← IO.mapTask (sync := true) (fun _ => do IO.println "sync dep (buffer)"; return 2) src
  let _ ← IO.wait src
  let _ ← IO.wait d
  IO.println s!"buffer: {(← r.get).trimAscii}"
