/-! Runtime test: files and the file system: write/read/append, handles
(getLine, read, rewind, truncate, flush, locks), directories, metadata,
rename/remove, and the `IO.Error`s of failing operations. All paths are
relative to the working directory (the test's build directory). -/

def showErr (act : IO α) (fmt : α → String) : IO String := do
  try return fmt (← act) catch e => return s!"error: {e}"

def main : IO Unit := do
  let dir : System.FilePath := "rtfiles-tmp"
  if ← dir.pathExists then IO.FS.removeDirAll dir
  IO.FS.createDir dir
  let f := dir / "a.txt"
  IO.FS.writeFile f "hello\nworld\nlast line without newline"
  IO.println s!"readFile {repr (← IO.FS.readFile f)}"
  IO.println s!"lines {← IO.FS.lines f}"
  IO.FS.withFile f .append fun h => h.putStrLn "\nappended"
  IO.println s!"after append {repr (← IO.FS.readFile f)}"
  let bytes ← IO.FS.readBinFile f
  IO.println s!"bytes {bytes.size} {bytes.toList.take 5}"
  IO.FS.writeBinFile (dir / "b.bin") (ByteArray.mk #[0, 1, 2, 255, 10, 13])
  IO.println s!"bin {(← IO.FS.readBinFile (dir / "b.bin")).toList}"
  -- handles
  let h ← IO.FS.Handle.mk f .read
  IO.println s!"getLine {repr (← h.getLine)} {repr (← h.getLine)}"
  IO.println s!"read 4 {(← h.read 4).toList}"
  h.rewind
  IO.println s!"after rewind {repr (← h.getLine)}"
  let rest ← h.readToEnd
  IO.println s!"readToEnd {rest.length}"
  IO.println s!"eof getLine {repr (← h.getLine)} read {(← h.read 3).size}"
  let w ← IO.FS.Handle.mk (dir / "c.txt") .write
  w.putStr "0123456789"
  w.flush
  w.lock
  w.unlock
  IO.println s!"tryLock {← w.tryLock}"
  w.unlock
  let rw ← IO.FS.Handle.mk (dir / "c.txt") .readWrite
  IO.println s!"rw read {(← rw.read 4).toList}"
  rw.truncate
  rw.flush
  IO.println s!"after truncate {repr (← IO.FS.readFile (dir / "c.txt"))}"
  -- metadata and directories
  let md ← f.metadata
  IO.println s!"size {md.byteSize} type {repr md.type} links {md.numLinks} isDir {← dir.isDir} {← f.isDir}"
  IO.println s!"dir type {repr (← dir.metadata).type} exists {← f.pathExists} {← (dir / "nope").pathExists}"
  IO.FS.createDirAll (dir / "sub" / "deeper")
  IO.FS.writeFile (dir / "sub" / "x.txt") "x"
  let entries ← dir.readDir
  IO.println s!"readDir {(entries.map (·.fileName)).qsort (· < ·)}"
  IO.FS.rename (dir / "sub" / "x.txt") (dir / "sub" / "y.txt")
  IO.println s!"renamed {← (dir / "sub" / "y.txt").pathExists} {← (dir / "sub" / "x.txt").pathExists}"
  IO.FS.removeFile (dir / "sub" / "y.txt")
  IO.println s!"removed {← (dir / "sub" / "y.txt").pathExists}"
  -- errors
  IO.println (← showErr (IO.FS.readFile (dir / "missing.txt")) id)
  IO.println (← showErr (IO.FS.Handle.mk (dir / "missing" / "x") .read) fun _ => "opened")
  IO.println (← showErr (IO.FS.Handle.mk (dir / "c.txt") .writeNew) fun _ => "opened")
  IO.println (← showErr (IO.FS.createDir dir) fun _ => "created")
  IO.println (← showErr (IO.FS.removeDir (dir / "sub")) fun _ => "removed")
  IO.println (← showErr (IO.FS.removeFile (dir / "missing.txt")) fun _ => "removed")
  IO.println (← showErr (IO.FS.rename (dir / "missing.txt") (dir / "z.txt")) fun _ => "renamed")
  IO.println (← showErr ((dir / "missing.txt").metadata) fun _ => "metadata")
  IO.println (← showErr (IO.FS.readFile dir) fun s => s)
  IO.println (← showErr (IO.FS.Handle.mk "bad\u0000name" .read) fun _ => "opened")
  IO.println (← showErr ((dir / "missing").readDir) fun _ => "listed")
  IO.FS.removeDirAll dir
  IO.println s!"cleaned {← dir.pathExists}"
