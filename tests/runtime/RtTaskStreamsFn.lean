/-! Runtime test: the standard streams used only through function values (a
record holding `IO.getStdout`/`IO.setStdout`, built by a `@[noinline]`
function) are per task too, and a panic goes into the stderr redirected
through the record. -/


structure Cfg where
  out : BaseIO IO.FS.Stream
  setOut : IO.FS.Stream → BaseIO IO.FS.Stream
  setErr : IO.FS.Stream → BaseIO IO.FS.Stream

@[noinline] def mkCfg (k : Nat) : Cfg :=
  if k > 100 then ⟨IO.getStderr, IO.setStderr, IO.setStdout⟩ else ⟨IO.getStdout, IO.setStdout, IO.setStderr⟩

def boom (n : Nat) : Nat := if n > 2 then panic! s!"boom {n}" else n

def main (args : List String) : IO Unit := do
  let cfg := mkCfg args.length
  let r ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let t ← IO.asTask (do
    let _ ← cfg.setOut (IO.FS.Stream.ofBuffer r)
    (← cfg.out).putStrLn "task: into its buffer")
  let _ ← IO.wait t
  (← cfg.out).putStrLn "main: real stdout"
  let b ← r.get
  (← cfg.out).putStrLn s!"buffer {(String.fromUTF8! b.data).quote}"
  -- a panic while stderr is redirected through the record
  let re ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let old ← cfg.setErr (IO.FS.Stream.ofBuffer re)
  (← cfg.out).putStrLn s!"boom {boom (3 + args.length)}"
  let _ ← cfg.setErr old
  (← cfg.out).putStrLn s!"stderr buffer {(String.fromUTF8! (← re.get).data).quote}"
