/-! Runtime test: C's `exit` flushes every open `FILE` (see
`RtExitFlush.pipe`, which prints the files afterwards): a handle kept in a
global reference, and a handle the caller still holds when
`IO.Process.exit` runs, lose no buffered output. -/

initialize gHandle : IO.Ref (Option IO.FS.Handle) ← IO.mkRef none

def work (h : IO.FS.Handle) : IO Unit := do
  h.putStrLn "line before exit"
  IO.println "stdout before exit"
  IO.Process.exit 7

def main : IO Unit := do
  let g ← IO.FS.Handle.mk "rtexitflush-global.txt" .write
  g.putStrLn "written via the global handle"
  gHandle.set (some g)
  let h ← IO.FS.Handle.mk "rtexitflush-local.txt" .write
  work h
  h.putStrLn "never"
