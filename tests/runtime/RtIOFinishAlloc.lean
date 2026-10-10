/-! Runtime test (review of the closure glue, hunt HSTR2-01; hunt HIOG2):
the glue of a fallible IO primitive allocates what native Lean allocates.
lean2rr passed the outcome to a prelude helper with two callbacks (`ok` and
the error builder), two closures at every call: a `putStr` to a handle made
3 allocations (natively 1, the result), a `getLine` 6 (natively 3). The
glue of `IO.getEnv` passed a `some` closure and looked the variable up
twice: 6 allocations for a set variable (natively 2), 1 for an unset one
(natively none).
- `put N`: N `putStr`s of one character to a handle on /dev/null.
- `line N`: N `getLine`s from a file of N short lines.
- `out N`: N `putStr`s of one character to the standard output stream.
- `fail N`: N `putStr`s to a read-only handle, each an error whose builder
  takes no file name (the error path of the glue: one call of the result
  type's error builder).
- `envset N`, `envunset N`: N `getEnv`s of `PATH` and of a variable that
  is never set.
- no mode: the five at N = 20, then the error paths and the payloads of
  the other glue arms (a missing file, a write to a read-only handle, a
  read from a write-only one, `readDir`, `metadata`, `createTempFile`,
  `getEnv` of a set and of an unset variable).
All paths are relative to the working directory (the test's build
directory). tests/runtime/alloc-check.sh compares the allocations at two
sizes (RtIOFinishAlloc.alloc). -/

def showErr (act : IO α) (fmt : α → String) : IO String := do
  try return fmt (← act) catch e => return s!"error: {e}"

def putLoop (h : IO.FS.Handle) : Nat → IO Unit
  | 0 => pure ()
  | k + 1 => do h.putStr "x"; putLoop h k

def lineLoop (h : IO.FS.Handle) : Nat → Nat → IO Nat
  | 0, acc => pure acc
  | k + 1, acc => do let l ← h.getLine; lineLoop h k (acc + l.length)

def outLoop (s : IO.FS.Stream) : Nat → IO Unit
  | 0 => pure ()
  | k + 1 => do s.putStr "x"; outLoop s k

def runPut (n : Nat) : IO Unit := do
  let h ← IO.FS.Handle.mk "/dev/null" .write
  putLoop h n
  IO.println s!"put {n}: done"

def runLine (n : Nat) : IO Unit := do
  let f : System.FilePath := "rtiofinishalloc-lines.txt"
  IO.FS.writeFile f (String.join (List.replicate n "ab\n"))
  let h ← IO.FS.Handle.mk f .read
  let t ← lineLoop h n 0
  IO.println s!"line {n}: {t} {repr (← h.getLine)}"
  IO.FS.removeFile f

def runOut (n : Nat) : IO Unit := do
  outLoop (← IO.getStdout) n
  IO.println s!"\nout {n}: done"

def failLoop (h : IO.FS.Handle) : Nat → Nat → IO Nat
  | 0, acc => pure acc
  | k + 1, acc => do
    let e ← try h.putStr "x"; pure 0 catch _ => pure 1
    failLoop h k (acc + e)

def runFail (n : Nat) : IO Unit := do
  let f : System.FilePath := "rtiofinishalloc-ro.txt"
  IO.FS.writeFile f "r"
  let h ← IO.FS.Handle.mk f .read
  IO.println s!"fail {n}: {← failLoop h n 0} errors"
  IO.FS.removeFile f

def envLoop (name : String) : Nat → Nat → IO Nat
  | 0, acc => pure acc
  | k + 1, acc => do
    let v ← IO.getEnv name
    envLoop name k (acc + if v.isSome then 1 else 0)

def unsetVar : String := "L2R_TEST_NEVER_SET_RTIOFINISHALLOC"

def runEnv (name : String) (n : Nat) : IO Unit := do
  IO.println s!"getEnv {n}: {← envLoop name n 0} set"

def main (args : List String) : IO Unit := do
  let n := (args[1]? >>= String.toNat?).getD 20
  match args.head? with
  | some "put" => runPut n
  | some "line" => runLine n
  | some "out" => runOut n
  | some "fail" => runFail n
  | some "envset" => runEnv "PATH" n
  | some "envunset" => runEnv unsetVar n
  | _ =>
    runPut n; runLine n; runOut n; runFail n; runEnv "PATH" n; runEnv unsetVar n
    let dir : System.FilePath := "rtiofinishalloc-tmp"
    if ← dir.pathExists then IO.FS.removeDirAll dir
    IO.FS.createDir dir
    let f := dir / "a.txt"
    IO.FS.writeFile f "one\ntwo\n"
    IO.println (← showErr (IO.FS.Handle.mk (dir / "missing.txt") .read) fun _ => "opened")
    let r ← IO.FS.Handle.mk f .read
    IO.println (← showErr r.getLine fun l => s!"{repr l}")
    -- (no `getLine` after this failed write: natively the handle's sticky
    -- error indicator would fail it, LB-41)
    IO.println (← showErr (r.putStr "x") fun _ => "written")
    let w ← IO.FS.Handle.mk (dir / "b.txt") .write
    IO.println (← showErr w.getLine fun l => s!"{repr l}")
    IO.println (← showErr (w.putStr "b") fun _ => "written")
    IO.println (← showErr (dir / "missing").readDir fun es => s!"{es.size} entries")
    IO.println (← showErr dir.readDir fun es => s!"{(es.map (·.fileName)).qsort (· < ·)}")
    IO.println (← showErr (dir / "missing.txt").metadata fun m => s!"{m.byteSize}")
    IO.println (← showErr f.metadata fun m => s!"size {m.byteSize} {repr m.type}")
    let (t, p) ← IO.FS.createTempFile
    t.putStr "temp"
    t.flush
    IO.println s!"temp exists {← p.pathExists} size {(← p.metadata).byteSize}"
    IO.FS.removeFile p
    IO.FS.removeDirAll dir
    IO.println s!"getEnv PATH set: {(← IO.getEnv "PATH").isSome}"
    IO.println s!"getEnv unset: {repr (← IO.getEnv unsetVar)}"
    IO.println s!"getEnv bad name: {repr (← IO.getEnv "PA=TH")} {repr (← IO.getEnv "")}"
