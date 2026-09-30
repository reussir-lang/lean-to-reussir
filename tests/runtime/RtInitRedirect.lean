/-! Runtime test: a stream redirection done by a module initializer (on the
process's main thread) is not in effect in `main` (on a thread of its own). -/

instance : Nonempty IO.FS.Stream.Buffer := ⟨{}⟩
initialize buf : IO.Ref IO.FS.Stream.Buffer ← IO.mkRef {}
initialize do
  let _ ← IO.setStdout (IO.FS.Stream.ofBuffer buf)
  IO.println "init: captured?"

def main : IO Unit := do
  IO.println "main: where does this go?"
  let s := String.fromUTF8! (← buf.get).data
  IO.eprintln s!"buffer = {s.quote}"
