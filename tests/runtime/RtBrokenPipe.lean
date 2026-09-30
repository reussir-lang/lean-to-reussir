/-! Runtime test: writing to a closed pipe (`$BIN | head -1`) is an IO error
(`resource vanished`, EPIPE) raised by the `putStr` whose buffer flush
fails; uncaught, it ends the program with exit code 1. -/

def main : IO Unit := do
  for i in [0:100000] do
    IO.println s!"line {i}"
  IO.eprintln "finished loop"
