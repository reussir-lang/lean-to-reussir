/-! Runtime test (glibc stdio model): write errors on /dev/full, and wrong-direction reads that
switch a write-only FILE to get mode (putting flag), with the handle kept
alive. -/

def showErr (act : IO α) (fmt : α → String) : IO String := do
  try return fmt (← act) catch e => return s!"error: {e}"

def rep (c : Char) (n : Nat) : String := String.ofList (List.replicate n c)

def size (p : System.FilePath) : IO Nat := return (← p.metadata).byteSize.toNat

def main : IO Unit := do
  let h ← IO.FS.Handle.mk "/dev/full" .write
  IO.println (← showErr (h.putStr "abc") fun _ => "put")
  IO.println (← showErr h.flush fun _ => "flushed")
  IO.println (← showErr h.flush fun _ => "flushed")
  IO.println (← showErr (h.putStr (rep 'x' 5000)) fun _ => "put")
  IO.println (← showErr (h.putStr (rep 'y' 100)) fun _ => "put")
  IO.println (← showErr (h.putStr (rep 'y' 4096)) fun _ => "put")
  IO.println (← showErr (h.putStr (rep 'z' 8192)) fun _ => "put")
  IO.println (← showErr h.getLine fun l => s!"line {repr l}")
  IO.println (← showErr (h.putStr "a") fun _ => "put")
  -- putting flag after a failed getLine on a live write-only handle
  let f : System.FilePath := "rvfull-tmp.txt"
  let w ← IO.FS.Handle.mk f .write
  w.putStr "hello"
  IO.println (← showErr w.getLine fun l => s!"line {repr l}")
  IO.println s!"after getLine: size {← size f}"
  w.putStr (rep 'x' 4096)
  IO.println s!"after 4096 more: size {← size f}"
  w.putStr "!"
  w.flush
  IO.println s!"after flush: size {← size f}"
  IO.FS.removeFile f
