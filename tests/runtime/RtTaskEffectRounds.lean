import Std.Internal.UV.Timer
/-! Runtime test: what natively runs on other threads while `main`
computes, through several steps, comes before `main`'s later output: a
relay of 10 tasks, each woken by the previous one's promise; 10 dependents
of a timer's promise; three tasks queued at once; a task's output before a
child process that `main` spawns; a thunk a task forces first (`main`
waits for its value). -/
def busy (ms : Nat) : IO Unit := do
  let start ← IO.monoMsNow
  while (← IO.monoMsNow) - start < ms do
    pure ()

def pr (s : String) : IO Unit := do IO.println s; (← IO.getStdout).flush

def eStr {α} [ToString α] : Except IO.Error α → String
  | .ok v => s!"ok {v}"
  | .error e => s!"error {e}"

@[noinline] def spin (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [0:n] do s := s + i % 7
  return s

def mkRelay : List (IO.Promise Nat) → Nat → IO (List (Task (Except IO.Error Unit)))
  | pin :: pout :: rest, i => do
    let t ← IO.asTask (do
      let v ← IO.wait pin.result!
      pr s!"relay {i} got {v}"
      pout.resolve (v + 1))
    return t :: (← mkRelay (pout :: rest) (i + 1))
  | _, _ => return []

def main : IO Unit := do
  let ps ← (List.range 11).mapM fun _ => IO.Promise.new (α := Nat)
  let ts ← mkRelay ps 0
  IO.sleep 20
  match ps with
  | p0 :: _ => p0.resolve 0
  | [] => pure ()
  busy 100
  pr "main after the relay"
  for t in ts do
    let _ ← IO.wait t
  let tm ← Std.Internal.UV.Timer.mk 20 false
  let p ← tm.next
  let ds ← (List.range 10).mapM fun _ => IO.mapTask (fun _ => pr "dep") p.result?
  busy 100
  pr "main after the timer's dependents"
  for t in ds do
    let _ ← IO.wait t
  let qs ← (List.range 3).mapM fun _ => IO.asTask (pr "task")
  busy 100
  pr "main after the queued tasks"
  for t in qs do
    let _ ← IO.wait t
  let t ← IO.asTask (do IO.sleep 20; pr "task before the child")
  IO.sleep 5
  busy 100
  let child ← IO.Process.spawn { cmd := "echo", args := #["child"] }
  let _ ← child.wait
  pr "main after the child"
  let _ ← IO.wait t
  let th : Thunk Nat := Thunk.mk fun _ => dbgTrace "thunk computes" fun _ => spin 3000000
  let t ← IO.asTask (do return th.get + 1)
  busy 30
  pr s!"main: {th.get}"
  pr s!"task: {eStr (← IO.wait t)}"
