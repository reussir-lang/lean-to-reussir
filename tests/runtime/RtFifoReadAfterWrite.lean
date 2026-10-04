/-! Runtime test (review RXT-01): output followed by a direct read on a
FIFO opened `readWrite`, after `getLine` read ahead. Before the read,
glibc (natively) would seek back over the read-ahead to write the output;
on a FIFO that seek fails (`ESPIPE`), and glibc's direct read then drops
the output and the read-ahead and reads on. lean2rr writes pending output
before a direct read (LB-02), but a failed seek is no failed write: the
read goes on as natively (it failed with `invalid seek`, and so did the
next read and flush). `RtFifoReadAfterWrite.pipe` makes the FIFO with
`mkfifo` in a `mktemp -d` directory and passes its path; the FIFO never
holds more than one page. -/

def step (name : String) (act : IO String) : IO Unit := do
  try
    let s ← act
    IO.println s!"{name}: ok {repr s}"
  catch e => IO.println s!"{name}: error {e}"

def main (args : List String) : IO Unit := do
  let p := args[0]!
  let h ← IO.FS.Handle.mk p .readWrite
  let w ← IO.FS.Handle.mk p .write
  w.putStr "abc\ndef\n"; w.flush
  step "getLine" h.getLine
  w.putStr ("jkl\n" ++ "".pushn 'x' 4092); w.flush
  step "putStr" (do h.putStr "ghi\n"; pure "")
  step "read 4096" (do
    let b ← h.read 4096
    let t := String.fromUTF8! b
    pure s!"{b.size} bytes, {String.ofList (t.toList.take 4)}")
  w.putStr "mnop"; w.flush
  step "read 4" (do let b ← h.read 4; pure (String.fromUTF8! b))
  step "flush" (do h.flush; pure "")
