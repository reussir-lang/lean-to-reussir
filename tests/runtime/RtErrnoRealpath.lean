/-! Runtime test: errno left by a successful `IO.FS.realPath` (glibc's
realpath leaves EINVAL from readlink on non-symlink components), observed
through a sticky error indicator on a read-only handle. -/

def main (args : List String) : IO Unit := do
  let f := "rv-errno.txt"
  IO.FS.writeFile f "line1\nline2\n"
  let h ← IO.FS.Handle.mk f .read
  try h.putStr "x"; h.flush catch e => IO.println s!"put: {e}"
  let p ← IO.FS.realPath "/usr/bin"
  IO.println s!"realpath {p} {args.length}"
  try
    let l ← h.getLine
    IO.println s!"line {repr l}"
  catch e => IO.println s!"getLine: {e}"
