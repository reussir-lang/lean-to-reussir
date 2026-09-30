/-! Runtime test: `IO.Process.exit` flushes buffered stdout and exits with
the given status, from inside nested IO code. -/

def work (n : Nat) : IO Unit := do
  for i in [0:n] do
    IO.println s!"working {i}"
    if i == 3 then
      IO.eprintln "exiting"
      IO.Process.exit 42

def main : IO Unit := do
  IO.print "partial line "
  work 10
  IO.println "never printed"
