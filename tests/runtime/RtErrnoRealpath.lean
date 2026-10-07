/-! Runtime test: errno left by a successful `IO.FS.realPath` (glibc's
realpath leaves EINVAL from readlink on non-symlink components). Natively
it shows through a sticky error indicator on a read-only handle: the
failed `putStr` sets it, and the later `getLine` reads its line and fails
with whatever errno holds then (`NAME.native.out`). lean2rr's `getLine`
clears the indicator first and reports only its own error (lean-runtime's
LB-41), so it returns the line (`NAME.l2r.out`). -/

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
