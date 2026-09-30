/-! Runtime test: the standard streams are per thread natively, and a task
runs on another thread than `main`: a task's `IO.setStdout` does not change
`main`'s stdout, a task does not print into `main`'s redirected stdout or
stderr (`IO.eprintln` and a panic in a task go to descriptor 2), a task
reads the real stdin while `main` has redirected it (NAME.stdin), and a task
still pending when `main` returns prints to the real stdout although `main`
left stdout redirected. -/

def boom (n : Nat) : Nat := if n > 2 then panic! s!"boom in task {n}" else n

def main (args : List String) : IO Unit := do
  let k := args.length
  -- A task's redirection stays in the task.
  let r0 ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  -- (It restores its stdout: natively a worker thread keeps its streams
  -- from one task to the next.)
  let t0 ← IO.asTask (do
    let o ← IO.setStdout (IO.FS.Stream.ofBuffer r0)
    IO.println "task into its buffer"
    let _ ← IO.wait (← IO.asTask (IO.println "nested task to real stdout"))
    let _ ← IO.setStdout o)
  let _ ← IO.wait t0
  IO.println s!"main after task; task buffer {(String.fromUTF8! (← r0.get).data).quote}"
  -- A task does not inherit main's redirected stdout.
  let t1 ← IO.asTask (do IO.sleep 30; IO.println "task to real stdout")
  let r1 ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let old ← IO.setStdout (IO.FS.Stream.ofBuffer r1)
  let _ ← IO.wait t1
  let _ ← IO.setStdout old
  IO.println s!"captured by main: {(String.fromUTF8! (← r1.get).data).quote}"
  -- Nor main's redirected stderr (eprintln and panics).
  let r2 ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let olde ← IO.setStderr (IO.FS.Stream.ofBuffer r2)
  let t2 ← IO.asTask (do IO.eprintln s!"eprintln in task {k}"; pure (boom (3 + k)))
  match ← IO.wait t2 with
  | .ok v => IO.println s!"task {v}"
  | .error e => IO.println s!"task error {e}"
  let _ ← IO.setStderr olde
  IO.println s!"stderr captured by main: {(String.fromUTF8! (← r2.get).data).quote}"
  -- Nor main's redirected stdin.
  let r3 ← IO.mkRef ({ data := "from buffer\n".toUTF8 } : IO.FS.Stream.Buffer)
  let t3 ← IO.asTask (do IO.sleep 20; (← IO.getStdin).getLine)
  let oldi ← IO.setStdin (IO.FS.Stream.ofBuffer r3)
  let l ← IO.wait t3
  let _ ← IO.setStdin oldi
  IO.println s!"task read {(l.toOption.getD "?").quote}"
  -- A task still pending when main returns prints to the real stdout.
  let r4 ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let _ ← IO.setStdout (IO.FS.Stream.ofBuffer r4)
  let _ ← IO.asTask (do IO.sleep 20; IO.println "late task prints")
