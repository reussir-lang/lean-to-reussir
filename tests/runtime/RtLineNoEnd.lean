/-! Runtime test (review RST3-02): `getLine` on a stream that never ends a line (stdin from
`/dev/zero`) under a memory limit: the line cannot be held, and the program ends with status 134
(natively `std::bad_alloc` aborts; here Rust's failed allocation aborts), its standard error
dropped by the `.pipe` (the two messages differ). The sink `getLine` appends to under the stream's
lock is infallible, as lean-runtime's contract asks: a sink that stopped instead made lean-runtime
read on for good. -/
def main : IO Unit := do
  IO.println "reading"
  (← IO.getStdout).flush
  let l ← (← IO.getStdin).getLine
  IO.println s!"got {l.length}"
