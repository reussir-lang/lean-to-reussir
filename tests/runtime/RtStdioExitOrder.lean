/-! Runtime test (glibc stdio model): when handle buffers reach a shared descriptor (handles on
/dev/stdout, stderr merged): at the last use (close) of a handle, and at
exit (newest handle first, then stdout). -/

def work (a b : IO.FS.Handle) : IO Unit := do
  a.putStr "alive-a\n"
  b.putStr "alive-b\n"
  IO.print "stdout-2\n"
  IO.eprintln "E3"
  IO.Process.exit 3

def main : IO Unit := do
  let h ← IO.FS.Handle.mk "/dev/stdout" .append
  h.putStr "B\n"
  IO.eprintln "E1"
  let h2 ← IO.FS.Handle.mk "/dev/stdout" .append
  h2.putStr "C\n"
  IO.eprintln "E2"
  IO.print "A\n"
  let a ← IO.FS.Handle.mk "/dev/stdout" .append
  let b ← IO.FS.Handle.mk "/dev/stdout" .append
  work a b
  a.putStr "never"
  b.putStr "never"
