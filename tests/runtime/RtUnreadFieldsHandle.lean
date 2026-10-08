/-!
Runtime test of the optimization `unread-fields` (off by default; this
test turns it on, `RtUnreadFieldsHandle.enable-opts`): a callback that
captured a file handle stays, in a program that makes resources. No code
reads the hook's `run`, but natively the closure keeps the handle open
while `hooks` lives, so its buffered write is not yet in the file when
the program reads it back. Left out, the closure would let the handle be
flushed and closed at its last other use (review of the pass, F3).
-/

structure Hook where
  name : String
  run : String → IO Unit

def main (args : List String) : IO Unit := do
  let h ← IO.FS.Handle.mk "out.txt" .write
  h.putStr s!"hello {args.length}"
  let hooks : Array Hook := #[{ name := "w", run := fun s => h.putStr s }]
  let content ← IO.FS.readFile "out.txt"
  IO.println s!"names {hooks.map (·.name)}, content '{content}'"
