/-! Runtime test: standard streams (buffered stdout, unbuffered stderr, in
order within each stream), stdin (`getLine` until EOF, `read`), `IO.Ref`
(get/set/modify/swap, aliasing), `dbgTrace`, `IO.print` of large outputs,
flushing, and the exit code from `main : IO UInt32`. -/

def countdown (r : IO.Ref Nat) : Nat → IO Unit
  | 0 => pure ()
  | n + 1 => do r.modify (· + n); countdown r n

partial def readLines (h : IO.FS.Stream) (acc : Array String) : IO (Array String) := do
  let line ← h.getLine
  if line.isEmpty then return acc else readLines h (acc.push line)

def main (args : List String) : IO UInt32 := do
  IO.println "hello"
  IO.print "no newline, "
  IO.println s!"args {args}"
  IO.eprintln "to stderr"
  IO.eprint "stderr without newline\n"
  let out ← IO.getStdout
  out.putStr "via stream\n"
  out.flush
  let err ← IO.getStderr
  err.putStrLn "stderr via stream"
  -- refs
  let r ← IO.mkRef (0 : Nat)
  countdown r 100
  IO.println s!"ref {← r.get}"
  r.set 7
  let old ← r.swap 9
  IO.println s!"swap {old} {← r.get}"
  let r2 := r
  r2.modify (· * 2)
  IO.println s!"alias {← r.get}"
  let arr ← IO.mkRef (#[] : Array Nat)
  for i in [0:10000] do
    arr.modify (·.push i)
  IO.println s!"array ref {(← arr.get).size} {(← arr.get).foldl (· + ·) 0}"
  let v ← r.modifyGet fun x => (x + 1, x + 2)
  IO.println s!"modifyGet {v} {← r.get}"
  let sref ← IO.mkRef "s"
  sref.modify (· ++ "t")
  IO.println s!"string ref {← sref.get} ptrEq {← r.ptrEq r2} {← r.ptrEq (← IO.mkRef 0)}"
  -- stdin
  let stdin ← IO.getStdin
  let first ← stdin.getLine
  IO.println s!"first line {repr first}"
  let bytes ← stdin.read 5
  IO.println s!"read 5 {bytes.toList}"
  let rest ← readLines stdin #[]
  IO.println s!"rest {rest.size} {rest.toList.take 3} last {repr rest.back?}"
  let eof ← stdin.getLine
  IO.println s!"eof {repr eof}"
  -- trace and a lot of output
  let t := dbgTrace "tracing" fun _ => "forty" ++ "-two"
  IO.println s!"traced {t}"
  for i in [0:3000] do
    IO.println s!"line {i} {"x".pushn '.' (i % 50)}"
  IO.eprintln "done"
  return 3
