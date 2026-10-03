/-! Runtime test: with `LEAN_MAIN_USE_THREAD=0` (see the `.pipe` file),
`main` runs on the module initializers' thread and keeps the stream
redirection an initializer left in place (translation plan §5.11; without
the variable `main` has a thread and streams of its own, RtInitRedirect).
A task still starts with the process's streams, as on a worker thread. -/

instance : Nonempty IO.FS.Stream.Buffer := ⟨{}⟩
initialize buf : IO.Ref IO.FS.Stream.Buffer ← IO.mkRef {}
initialize do
  let _ ← IO.setStdout (IO.FS.Stream.ofBuffer buf)
  IO.println "init: captured"

def main : IO Unit := do
  IO.println "main: captured too"
  let t ← IO.asTask (IO.println "task: process stdout")
  let _ ← IO.wait t
  let s := String.fromUTF8! (← buf.get).data
  IO.eprintln s!"buffer = {s.quote}"
