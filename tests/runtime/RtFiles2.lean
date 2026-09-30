/-! Runtime test: file-system corner cases.
* Operations Lean implements with libuv (`removeFile`, `hardLink`,
  `metadata`) report libuv's negated error codes and messages.
* `realPath` failures are always "no such file or directory".
* Paths with NUL bytes are invalid arguments, never successes.
* Writing to a handle opened for reading (and reading from one opened for
  writing) fails at once with `EBADF`.
* Handle writes are buffered in `st_blksize` blocks as glibc does, so
  another reader sees the same prefix of the file.
* End of file on `read`/`getLine`. -/

def showErr (act : IO α) (fmt : α → String) : IO String := do
  try return fmt (← act) catch e => return s!"error: {e}"

def main : IO Unit := do
  let dir : System.FilePath := "rtfiles2-tmp"
  if ← dir.pathExists then IO.FS.removeDirAll dir
  IO.FS.createDir dir
  let f := dir / "a.txt"
  IO.FS.writeFile f "0123456789"
  IO.FS.createDir (dir / "d")
  -- libuv errors
  IO.println (← showErr (IO.FS.removeFile (dir / "d")) fun _ => "removed")
  IO.println (← showErr (IO.FS.hardLink f f) fun _ => "linked")
  IO.println (← showErr ((f / "x").metadata) fun _ => "metadata")
  IO.println (← showErr ((f / "x").symlinkMetadata) fun _ => "metadata")
  IO.println (← showErr (IO.FS.removeFile (f / "x")) fun _ => "removed")
  -- realPath
  IO.println (← showErr (IO.FS.realPath (f / "x")) fun p => p.toString)
  IO.println (← showErr (IO.FS.realPath (dir / "missing")) fun p => p.toString)
  -- NUL bytes
  let bad : System.FilePath := "rtfiles2\u0000tmp"
  IO.println (← showErr bad.readDir fun a => s!"listed {a.size}")
  IO.println (← showErr bad.metadata fun _ => "metadata")
  IO.println (← showErr (IO.FS.realPath bad) fun p => p.toString)
  IO.println s!"isDir {← bad.isDir} pathExists {← bad.pathExists}"
  IO.println (← showErr (IO.FS.rename bad "x\u0000y") fun _ => "renamed")
  IO.println (← showErr (IO.FS.hardLink bad "x\u0000y") fun _ => "linked")
  IO.println (← showErr (IO.FS.removeFile bad) fun _ => "removed")
  -- wrong direction
  let r ← IO.FS.Handle.mk f .read
  IO.println (← showErr (r.putStr "x") fun _ => "put")
  IO.println (← showErr (r.write (ByteArray.mk #[1, 2])) fun _ => "wrote")
  IO.println (← showErr r.flush fun _ => "flushed")
  IO.println (← showErr r.getLine fun l => s!"line {repr l}")
  let w ← IO.FS.Handle.mk (dir / "w.txt") .write
  IO.println (← showErr w.getLine fun l => s!"line {repr l}")
  IO.println (← showErr (w.read 3) fun b => s!"read {b.size}")
  IO.println (← showErr (w.putStr "ok") fun _ => "put")
  w.flush
  IO.println s!"w.txt {repr (← IO.FS.readFile (dir / "w.txt"))}"
  -- buffering as glibc: what another reader sees before a flush
  let b ← IO.FS.Handle.mk (dir / "b.txt") .write
  b.putStr (String.ofList (List.replicate 5000 'x'))
  IO.println s!"after 5000: {(← (dir / "b.txt").metadata).byteSize}"
  b.putStr (String.ofList (List.replicate 70000 'y'))
  IO.println s!"after 75000: {(← (dir / "b.txt").metadata).byteSize}"
  for _ in [0:100] do b.putStr "line\n"
  IO.println s!"after lines: {(← (dir / "b.txt").metadata).byteSize}"
  b.flush
  IO.println s!"after flush: {(← (dir / "b.txt").metadata).byteSize}"
  -- end of file
  let e ← IO.FS.Handle.mk f .read
  IO.println s!"read 100: {(← e.read 100).size}, again: {(← e.read 100).size}, line {repr (← e.getLine)}"
  e.rewind
  IO.println s!"after rewind: {(← e.read 4).size} line {repr (← e.getLine)} {repr (← e.getLine)}"
  IO.FS.removeDirAll dir
  IO.println s!"cleaned {← dir.pathExists}"
