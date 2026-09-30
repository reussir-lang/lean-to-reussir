/-! Runtime test: `IO.Process.forceExit` ends the process at once
(`std::_Exit`): buffered stdout is lost (stdout is a file here), stderr
(unbuffered) is not. -/

def main : IO Unit := do
  IO.println "buffered, lost"
  IO.eprintln "stderr, kept"
  IO.Process.forceExit 3
