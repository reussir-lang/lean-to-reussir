/-! Runtime test (glibc stdio model): `fflush(stdin)` seeks a seekable stdin back to the
logical position (RvStdinFlush.pipe runs `head` after the program). -/

def main : IO Unit := do
  let stdin ← IO.getStdin
  let l ← stdin.getLine
  stdin.flush
  IO.println s!"got {repr l}"
