/-! Runtime test: input directly after output on one handle, an intended
difference from native (plan §10, "Runtime: Lean bugs we do not
reproduce", LB-02 in lean-runtime's docs/lean-bugs.md).
Natively `Handle.read` is glibc's `fread`, and a read of at least one
buffer right after output discards the pending output instead of writing
it (C11 7.21.5.3p7 leaves output directly followed by input undefined): the
written bytes never reach the file. lean2rr writes them first, then reads
from the cursor, or fails with native's EBADF on a write-only handle. The
expectation files pin both sides: `RtReadAfterWrite.native.out` (native,
the bytes lost) and `RtReadAfterWrite.l2r.out`.
- F: write-only handle, `putStr` then `read 5000` (fails);
- A: append handle, the same;
- G: read-write handle on "0123456789", `putStr` then `read 5000`;
- S: the same with `read 4` (glibc flushes for a small read: no loss);
- O: standard output (a file here), `print` then `read 5000` (fails).
The written text comes from the command line. -/

def showErr (act : IO α) (fmt : α → String) : IO String := do
  try return fmt (← act) catch e => return s!"error: {e}"

def main (args : List String) : IO Unit := do
  let t := args[0]!
  let dir : System.FilePath := "rtreadafterwrite-tmp"
  if ← dir.pathExists then IO.FS.removeDirAll dir
  IO.FS.createDir dir
  let f := dir / "f.txt"
  let w ← IO.FS.Handle.mk f .write
  w.putStr t
  let r ← showErr (w.read 5000) fun b => s!"read {b.size}"
  w.flush
  IO.println s!"F: {r}; contents {repr (← IO.FS.readFile f)}"
  let a := dir / "a.txt"
  IO.FS.writeFile a "0123"
  let ah ← IO.FS.Handle.mk a .append
  ah.putStr t
  let r ← showErr (ah.read 5000) fun b => s!"read {b.size}"
  ah.flush
  IO.println s!"A: {r}; contents {repr (← IO.FS.readFile a)}"
  let g := dir / "g.txt"
  IO.FS.writeFile g "0123456789"
  let h ← IO.FS.Handle.mk g .readWrite
  h.putStr t
  let b ← h.read 5000
  h.flush
  IO.println s!"G: read {repr (String.fromUTF8! b)}; contents {repr (← IO.FS.readFile g)}"
  let s := dir / "s.txt"
  IO.FS.writeFile s "0123456789"
  let h ← IO.FS.Handle.mk s .readWrite
  h.putStr t
  let b ← h.read 4
  h.flush
  IO.println s!"S: read {repr (String.fromUTF8! b)}; contents {repr (← IO.FS.readFile s)}"
  IO.FS.removeDirAll dir
  let out ← IO.getStdout
  out.flush
  IO.print s!"O: {t} printed; "
  let r ← showErr (out.read 5000) fun b => s!"read {b.size}"
  IO.println s!"{r}"
