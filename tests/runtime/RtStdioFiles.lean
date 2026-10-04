/-! Review probes: glibc FILE behaviours of file handles. -/

def showErr (act : IO α) (fmt : α → String) : IO String := do
  try return fmt (← act) catch e => return s!"error: {e}"

def rep (c : Char) (n : Nat) : String := String.ofList (List.replicate n c)

def size (p : System.FilePath) : IO Nat := return (← p.metadata).byteSize.toNat

def countW (s : String) : Nat := s.foldl (fun n c => if c == 'W' then n + 1 else n) 0

def lines (n : Nat) : String := Id.run do
  let mut s := ""
  for i in [0:n] do
    let d := toString (10000 + i)
    s := s ++ "line " ++ (d.drop 1).toString ++ "\n"
  return s

def main : IO Unit := do
  let dir : System.FilePath := "rvfiles-tmp"
  if ← dir.pathExists then IO.FS.removeDirAll dir
  IO.FS.createDir dir
  -- B: read-ahead of a read handle (glibc: one 4096-byte block)
  let f := dir / "b.txt"
  IO.FS.writeFile f (lines 2000)
  let h ← IO.FS.Handle.mk f .read
  let l1 ← h.getLine
  IO.FS.writeFile f "short\n"
  let mut n := 0
  let mut last := ""
  repeat
    let l ← h.getLine
    if l.isEmpty then break
    n := n + 1
    last := l
  IO.println s!"B: first {repr l1}, then {n} lines, last {repr last}"
  -- C: rewind within the buffer reuses it
  let f := dir / "c.txt"
  IO.FS.writeFile f "old content\n"
  let h ← IO.FS.Handle.mk f .read
  let a ← h.getLine
  IO.FS.writeFile f "NEW CONTENT\n"
  h.rewind
  let b ← h.getLine
  IO.println s!"C: {repr a} then after rewind {repr b}"
  -- D: flush of a read handle drops the read-ahead
  let f := dir / "d.txt"
  IO.FS.writeFile f "one\ntwo\n"
  let h ← IO.FS.Handle.mk f .read
  let a ← h.getLine
  IO.FS.writeFile f "ONE\nTWO\n"
  h.flush
  let b ← h.getLine
  IO.println s!"D: {repr a} then after flush {repr b}"
  -- E: a failed small read on a write-only handle flushes it
  let f := dir / "e.txt"
  let w ← IO.FS.Handle.mk f .write
  w.putStr "hello"
  let r ← showErr (w.read 1) fun b => s!"read {b.size}"
  IO.println s!"E: {r}; size {← size f}"
  w.putStr (rep 'x' 4096)
  IO.println s!"E: after 4096 more: size {← size f}"
  -- E2: failed getLine on a write-only handle
  let f := dir / "e2.txt"
  let w ← IO.FS.Handle.mk f .write
  w.putStr "hello"
  let r ← showErr w.getLine fun l => s!"line {repr l}"
  IO.println s!"E2: {r}; size {← size f}"
  -- F and G (a large read right after output, which glibc lets drop the
  -- pending bytes and lean2rr does not: LB-02) are in RtReadAfterWrite.
  -- H: sticky end of file and large reads
  let f := dir / "h.txt"
  IO.FS.writeFile f (rep 'a' 10)
  let h ← IO.FS.Handle.mk f .read
  let b1 ← h.read 100
  IO.println s!"H: read {b1.size}"
  let ap ← IO.FS.Handle.mk f .append
  ap.putStr (rep 'b' 10)
  ap.flush
  let b2 ← h.read 5000
  let b3 ← h.read 5000
  IO.println s!"H: after append read 5000 -> {b2.size}, again {b3.size}"
  -- I: readWrite, read 4000 then write 200: what reaches the file at once
  let f := dir / "i.txt"
  IO.FS.writeFile f (rep 'x' 10000)
  let h ← IO.FS.Handle.mk f .readWrite
  let _ ← h.read 4000
  h.putStr (rep 'W' 200)
  IO.println s!"I: W visible before flush {countW (← IO.FS.readFile f)}"
  h.flush
  IO.println s!"I: W visible after flush {countW (← IO.FS.readFile f)}"
  -- J: truncate does not flush (write mode)
  let f := dir / "j.txt"
  let w ← IO.FS.Handle.mk f .write
  w.putStr "hello"
  w.truncate
  IO.println s!"J: after truncate {repr (← IO.FS.readFile f)}"
  w.flush
  IO.println s!"J: after flush {repr (← IO.FS.readFile f)}"
  -- K: truncate of an append handle with pending output
  let f := dir / "k.txt"
  IO.FS.writeFile f "base"
  let w ← IO.FS.Handle.mk f .append
  w.putStr "abc"
  w.truncate
  w.flush
  IO.println s!"K: {repr (← IO.FS.readFile f)}"
  -- L: rewind of a write handle then exact-block write
  let f := dir / "l.txt"
  let w ← IO.FS.Handle.mk f .write
  w.putStr "hello"
  w.rewind
  w.putStr (rep 'y' 4096)
  IO.println s!"L: after rewind + 4096: size {← size f}"
  w.flush
  IO.println s!"L: after flush: size {← size f}"
  IO.FS.removeDirAll dir
  IO.println "done"
