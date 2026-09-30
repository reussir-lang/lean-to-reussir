/-! Runtime test (glibc stdio model): stdin read-ahead seen by the next process on the same
descriptor (RvStdinAhead.pipe runs `head` after the program). -/

def main : IO Unit := do
  let stdin ← IO.getStdin
  let l ← stdin.getLine
  IO.println s!"got {repr l}"
