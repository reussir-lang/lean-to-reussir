/-! Runtime test (glibc stdio model): writing zero bytes to stdin is a no-op natively (fwrite
returns at once), so it must not set stdin's error indicator. Likewise
reading zero bytes from stdout. Natively the following `getLine` would
fail with a set indicator; lean2rr's `getLine` clears it first and reports
only its own error (lean-runtime's LB-41), so this test now checks that
the zero-byte operations succeed and that the line is read. -/

def main : IO Unit := do
  let stdin ← IO.getStdin
  stdin.putStr ""
  stdin.write ByteArray.empty
  let l ← stdin.getLine
  IO.println s!"got {repr l}"
  let out ← IO.getStdout
  let b ← out.read 0
  IO.println s!"read 0 from stdout: {b.size}"
