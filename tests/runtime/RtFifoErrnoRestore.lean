/-! Runtime test (review RXT-06): `errno` after a direct read whose
pending output cannot be written. On a FIFO opened `readWrite` and read
ahead, lean2rr's write-out before a direct read (LB-02) seeks back over the
read-ahead, which fails with `ESPIPE`; the bytes are dropped and the read
goes on, as natively, and `errno` must be left as it was: native's direct
read makes no seek. A later error report that reads `errno` shows it:
`getLine` on a handle whose error indicator is set (here by a write beyond
the file size limit, `EFBIG`) reports the current `errno`, natively 27
(lean2rr reported 29). `RtFifoErrnoRestore.pipe` ignores `SIGXFSZ`, sets
`ulimit -f 1` (1024 bytes) and passes a FIFO made with `mkfifo` in a
`mktemp -d` directory; the FIFO never holds more than one page. -/

def step (name : String) (act : IO String) : IO Unit := do
  try
    let s ← act
    IO.println s!"{name}: ok {s}"
  catch e => IO.println s!"{name}: error {e}"

def main (args : List String) : IO Unit := do
  IO.FS.writeFile "b.txt" "line\n"
  let b ← IO.FS.Handle.mk "b.txt" .readWrite
  b.putStr ("".pushn 'a' 2000)
  step "b flush" (do b.flush; pure "")
  let p := args[0]!
  let h ← IO.FS.Handle.mk p .readWrite
  let w ← IO.FS.Handle.mk p .write
  w.putStr "abc\ndef\n"; w.flush
  step "getLine" (do let l ← h.getLine; pure (repr l).pretty)
  w.putStr ("jkl\n" ++ "".pushn 'x' 4092); w.flush
  step "putStr" (do h.putStr "ghi\n"; pure "")
  step "read 4096" (do let b ← h.read 4096; pure s!"{b.size} bytes")
  b.rewind
  step "b getLine" (do let l ← b.getLine; pure s!"{l.length} chars")
