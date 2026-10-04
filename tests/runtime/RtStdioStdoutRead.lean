/-! Runtime test (glibc stdio model): reading from stdout (wrong direction). glibc's getc/fread
switch the FILE to get mode first: a small read flushes stdout, a large
(>= one block) fread natively discards the buffered output (`c`), which
lean2rr writes first instead (LB-02, plan §10 "Runtime: Lean bugs we do not
reproduce"): RtStdioStdoutRead.native.out and RtStdioStdoutRead.l2r.out pin
both. RvStdoutRead.pipe merges stderr into stdout. -/

def main : IO Unit := do
  IO.print "a\n"
  let out ← IO.getStdout
  let _ ← (try out.getLine catch _ => pure "")
  IO.eprintln "b"
  IO.print "c\n"
  let _ ← (try out.read 5000 catch _ => pure ByteArray.empty)
  IO.eprintln "d"
  IO.print "e\n"
