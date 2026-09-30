/-! Runtime test: standard streams that are `/dev/null` opened read-write
(`RtStdioDevNullRW.pipe`, as Python's `subprocess.DEVNULL` gives them) are
ordinary open streams, not the closed descriptors that Rust's runtime also
replaces with a read-write `/dev/null` before `main`. -/
def main : IO Unit := do
  try
    IO.println "to /dev/null"
    (← IO.getStdout).flush
    IO.eprintln "stdout ok"
  catch e => IO.eprintln s!"stdout: {e}"
  try
    let l ← (← IO.getStdin).getLine
    IO.eprintln s!"stdin {repr l}"
  catch e => IO.eprintln s!"stdin: {e}"
  let c ← IO.Process.spawn { cmd := "sh", args := #["-c", "echo child && echo 'child: stdout ok' >&2"] }
  IO.eprintln s!"child {← c.wait}"
