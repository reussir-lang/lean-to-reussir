import Std.Sync
/-! Runtime test (review RS7-02; lean-runtime's AR-39): a recursive mutex
that a module initializer locked and kept, locked again by `main`. A
lock's owner is an OS thread. Natively the initializers run on the
process's main thread, and with `LEAN_MAIN_USE_THREAD=0` `main` runs there
too, so its lock is nested and the program completes; on a thread of its
own (the default) `main` waits for the initializers' thread forever, also
with `LEAN_NUM_THREADS=0`. The `.pipe` file runs the two shapes under
`timeout 5` and prints each status: `LEAN_MAIN_USE_THREAD=0` (status 0),
and `main` on its own thread with `LEAN_NUM_THREADS=0` (no task manager;
status 124). Output is flushed before the second lock, so that a hang
keeps it.

Was (lean-runtime f618102 and before; fixed in 471f458, fixes-7): the
owner told an initializer from `main` by the scheduler having started, not
by the OS thread:
with `LEAN_MAIN_USE_THREAD=0` `main` waited for itself forever (status
124), and with `LEAN_NUM_THREADS=0` on its own thread it took the lock
(status 0). -/

initialize gRec : Std.BaseRecursiveMutex ← do
  let m ← Std.BaseRecursiveMutex.new
  m.lock
  IO.println "init: locked"
  pure m

def main : IO Unit := do
  IO.println "main: locking again"
  (← IO.getStdout).flush
  gRec.lock
  IO.println "main: locked"
  gRec.unlock
  gRec.unlock
  IO.println "main: unlocked twice"
