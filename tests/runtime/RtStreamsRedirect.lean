/-! Runtime test: the runtime's diagnostics go to the *current* stderr
stream, as native `io_eprintln`: `panic!`, `dbgTrace`
and `allocprof` printed while stderr is redirected to a buffer end up in
the buffer. (The runtime's own panics: `RtStreamsRedirectOob`.) -/

def boom (n : Nat) : Nat := if n > 2 then panic! s!"boom {n}" else n

def main (args : List String) : IO Unit := do
  let k := args.length
  let buf ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let old ← IO.setStderr (IO.FS.Stream.ofBuffer buf)
  let xs : Array Nat := #[1, 2]
  IO.println s!"panic {boom (3 + k)}"
  let t := dbgTrace s!"traced {k}" fun _ => k + 1
  IO.println s!"trace {t}"
  let r ← allocprof "profiled" (pure (k + 7))
  IO.println s!"allocprof {r}"
  IO.eprintln "explicit eprintln"
  let _ ← IO.setStderr old
  let b ← buf.get
  IO.println s!"captured stderr:\n{String.fromUTF8! b.data}"
  IO.eprintln "back on real stderr"
  IO.println s!"after {xs[7 + k]!}"
