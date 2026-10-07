import Std.Sync

/-! Runtime test (lean2rr's review HR-03): each of `Std.Sync`'s try
functions right after a pipe handle's drop whose `fclose` blocks natively
until the child reads (about half a second), while a dedicated task takes
the lock at 150 ms: natively the lock is taken by then, and the try fails
("false" four times). lean2rr's drop hands the last byte to a writer thread
of lean-runtime and waits for it at the end of the free (lean-runtime's
drain-end hook `sched::after_drain`); since lean-runtime's fixes-14 the try
functions also wait for the context's writers first, as their blocking
counterparts do. Before, neither waited: the try took the lock before the
task could ("true"), and the task then waited for the lock forever.
lean-runtime's case `process/handoff_then_try_lock`. Needs `sh`, `sleep`,
`cat` and the default pipe capacity (64 KiB). -/

open Std

def round (name : String) (take : IO Unit) (attempt : IO Bool) : IO Unit := do
  let started ← IO.Promise.new (α := Unit)
  let taker ← IO.asTask (prio := .dedicated) do
    started.resolve ()
    IO.sleep 150
    take
  let _ ← IO.wait started.result?
  let child ← IO.Process.spawn
    { cmd := "sh", args := #["-c", "sleep 0.5; cat > /dev/null"], stdin := .piped }
  let (stdin, child) ← child.takeStdin
  stdin.write (ByteArray.mk (Array.replicate 65536 120))
  stdin.flush
  stdin.putStr "x"
  -- `stdin`'s last use: it is closed here, before the try
  let got ← attempt
  IO.println s!"{name}: {got}"
  let _ ← IO.wait taker
  let _ ← child.wait

def main : IO Unit := do
  let m ← BaseMutex.new
  round "BaseMutex.tryLock" m.lock m.tryLock
  let r ← BaseRecursiveMutex.new
  round "BaseRecursiveMutex.tryLock" r.lock r.tryLock
  let s ← BaseSharedMutex.new
  round "BaseSharedMutex.tryWrite" s.write s.tryWrite
  let w ← BaseSharedMutex.new
  round "BaseSharedMutex.tryRead" w.write w.tryRead
