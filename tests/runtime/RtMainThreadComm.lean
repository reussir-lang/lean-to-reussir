/-! Runtime test (switch step 7): `main` runs on a thread of its own, as
Lean's `lean_run_main` runs it (lean-runtime's `io::startup::run_main`),
and that thread has no name of its own: it keeps the process's, as
natively (`lthread` names none). With `LEAN_MAIN_USE_THREAD=0` (the second
run of the `.pipe` file) `main` runs on the process's main thread.

Was (dev 698e92b): lean2rr named the thread `main`, so its
`/proc/thread-self/comm` differed from the process's `/proc/self/comm`
("has the process's name: false" in the first run). -/

def main : IO Unit := do
  let proc ← IO.FS.readFile "/proc/self/comm"
  let thread ← IO.FS.readFile "/proc/thread-self/comm"
  -- `/proc/thread-self` is the link `<pid>/task/<tid>`
  let path ← IO.FS.realPath "/proc/thread-self"
  let parts := path.toString.splitOn "/"
  let own := match parts with
    | ["", "proc", pid, "task", tid] => pid != tid
    | _ => false
  IO.println s!"main runs on a thread of its own: {own}"
  IO.println s!"main's thread has the process's name: {proc == thread}"
