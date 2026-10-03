-- `sync` dependents of a task reached through uniform code. A task stored in
-- a polymorphically recursive inductive (`Nest`) has another representation
-- there, so lean2rr converts it lazily: the uniform code holds a copy that
-- forces the original. Forcing the copy runs the original, whose end runs
-- its `sync` dependents at once, inside the copy's forcing; they read the
-- task through the copy, which natively is the finished task itself. (This
-- hung: the copy counted as running until its own forcing ended.)
-- `main` prints after waiting for the dependents (natively the `sync` ones
-- run on the thread that finishes the task, while `main` wakes up), and the
-- non-`sync` ones are waited for one by one before the task is forced (two
-- workers may run them at once), so that the output does not depend on
-- timing.

inductive Nest : Type → Type 1 where
  | here {α : Type} (t : Task α) : Nest α
  | deeper {α : Type} (n : Nest (List α)) : Nest α

partial def Nest.force {α : Type} [ToString α] : Nest α → String
  | .here t => s!"{t.get}"
  | .deeper n => n.force

-- Forced now (an IO action, which the compiler does not move after the
-- waits that follow, as it may move a pure `let`).
@[noinline] def forceNow (n : Nest Nat) : IO String := pure n.force

-- `IO.mapTask`: an IO dependent.
partial def Nest.dep {α : Type} [ToString α] (l : String) (sync : Bool) :
    Nest α → IO (Task (Except IO.Error Unit))
  | .here t => IO.mapTask (sync := sync) (fun v => IO.println s!"{l}: dep sees {v}") t
  | .deeper n => n.dep l sync

-- `IO.bindTask`: an IO dependent continuing as the task its function returns.
partial def Nest.bind {α : Type} [ToString α] (l : String) (sync : Bool) :
    Nest α → IO (Task (Except IO.Error String))
  | .here t => IO.bindTask (sync := sync) t fun v => do
      IO.println s!"{l}: bind sees {v}"
      return Task.pure (.ok s!"bound {v}")
  | .deeper n => n.bind l sync

-- `Task.map`: a pure dependent.
partial def Nest.pmap {α : Type} [ToString α] (sync : Bool) : Nest α → Task String
  | .here t => t.map (sync := sync) fun v => s!"mapped {v}"
  | .deeper n => n.pmap sync

def source (l : String) (k : Nat) : IO (Task (List (List Nat))) := do
  let src ← IO.asTask (do IO.sleep 20; IO.println s!"{l}: src runs"; return k)
  return src.map fun x => [[x.toOption.getD 0, k + 1], [k + 2]]

-- The task two levels down, as `Nest Nat` sees it.
def nest (t : Task (List (List Nat))) : Nest Nat := .deeper (.deeper (.here t))

def check (l : String) (sync : Bool) (k : Nat) : IO Unit := do
  let n := nest (← source l k)
  let d ← n.dep l sync
  unless sync do
    let _ ← IO.wait d
  let b ← n.bind l sync
  unless sync do
    let _ ← IO.wait b
  let m := n.pmap sync
  let s ← forceNow n
  let _ ← IO.wait d
  let r ← IO.wait b
  IO.println s!"{l}: force {s}"
  IO.println s!"{l}: {r.toOption.getD "error"}, {m.get}"
  IO.println s!"{l}: force again {n.force}"

-- One level down (`Nest (List Nat)` holds the task) and only an IO dependent.
def checkOne (l : String) (sync : Bool) : IO Unit := do
  let src ← IO.asTask (do IO.sleep 20; IO.println s!"{l}: src runs"; return 3)
  let t : Task (List Nat) := src.map fun x => [x.toOption.getD 0, 4]
  let n : Nest Nat := .deeper (.here t)
  let d ← n.dep l sync
  unless sync do
    let _ ← IO.wait d
  let s ← forceNow n
  let _ ← IO.wait d
  IO.println s!"{l}: force {s}"
  IO.println s!"{l}: end"

def main (args : List String) : IO Unit := do
  -- Not a constant: lean2rr cannot specialize on it.
  let sync := args.length == 0
  checkOne "one sync" sync
  checkOne "one async" (!sync)
  check "sync" sync 10
  check "async" (!sync) 20
