/-! Runtime test: standard streams that are closed when the program starts
(`RtClosedStreams.pipe` closes stdout and stdin). Native Lean's runtime
descriptors take their place, so writes and reads fail with `EINVAL`; the
errors are caught and reported on stderr. -/

def main : IO Unit := do
  try
    IO.println "to closed stdout"
    (← IO.getStdout).flush
    IO.eprintln "no error on stdout"
  catch e => IO.eprintln s!"stdout: {e}"
  try
    let l ← (← IO.getStdin).getLine
    IO.eprintln s!"read {repr l}"
  catch e => IO.eprintln s!"stdin: {e}"
  try
    let b ← (← IO.getStdin).read 10
    IO.eprintln s!"read bytes {b.size}"
  catch e => IO.eprintln s!"stdin read: {e}"
  IO.eprintln "done"
