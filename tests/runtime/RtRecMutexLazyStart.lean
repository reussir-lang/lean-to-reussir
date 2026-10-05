import Std.Sync
/-! Runtime test (review RS4-05): a recursive mutex made by a module
initializer, locked by `main` before the program's first task, then locked
again (nested) by `main` after it. Natively `main` holds the lock twice:
"locked once", "locked twice", "task: 42". lean-runtime's lock owner tells
`main` apart from the initializers by its scheduler having started; lean2rr
starts the scheduler lazily (at the first task, promise, `Std.Sync` object,
timer or socket after `main` started), so `main`'s first lock, taken before
its first task, had another owner than its nested one, and `main` waited for
itself forever. Every `Std.Sync` operation now starts the scheduler once
`main` runs (lean-runtime's `ensure_started`, called by each of its `sync`
methods; leanrt's `settle` until switch step 7). -/

initialize gm : Std.BaseRecursiveMutex ← Std.BaseRecursiveMutex.new

def main : IO Unit := do
  gm.lock
  IO.println "locked once"
  -- The program's first task: lean2rr starts lean-runtime's scheduler here.
  let t ← IO.asTask (pure (42 : Nat))
  gm.lock
  IO.println "locked twice"
  gm.unlock
  gm.unlock
  match ← IO.wait t with
  | .ok v => IO.println s!"task: {v}"
  | .error e => IO.println s!"task failed: {e}"
