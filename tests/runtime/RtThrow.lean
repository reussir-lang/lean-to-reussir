/-! Runtime test: an uncaught `IO` exception after buffered output
(`uncaught exception: ...` on stderr, exit code 1, stdout still flushed),
plus exceptions caught with `try`/`catch` and `IO.Error` formatting. -/

def mayFail (n : Nat) : IO Nat := do
  if n > 3 then throw (IO.userError s!"too big: {n}") else pure (n * 10)

def main (args : List String) : IO Unit := do
  for i in [0:5] do
    try
      let v ← mayFail i
      IO.println s!"ok {v}"
    catch e =>
      IO.println s!"caught {e}"
  let r ← (mayFail 9).toBaseIO
  match r with
  | .ok v => IO.println s!"value {v}"
  | .error e => IO.println s!"error value {e}"
  IO.println s!"errors {IO.userError "u"} | {(IO.Error.noFileOrDirectory "f.txt" 2 "No such file")}"
  IO.println "about to throw"
  let _ ← mayFail (args.length + 100)
  IO.println "unreachable"
