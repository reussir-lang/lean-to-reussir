/-! Runtime test: the runtime's own panics (`index out of bounds`) go to the
*current* stderr stream, as native `io_eprintln`. -/

def main (args : List String) : IO Unit := do
  let k := args.length
  let buf ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let old ← IO.setStderr (IO.FS.Stream.ofBuffer buf)
  let xs : Array Nat := #[1, 2]
  IO.println s!"oob {xs[5 + k]!}"
  let _ ← IO.setStderr old
  let b ← buf.get
  IO.println s!"captured stderr: {repr (String.fromUTF8! b.data)}"
