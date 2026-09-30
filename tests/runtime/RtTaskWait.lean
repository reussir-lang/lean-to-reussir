/-! Runtime test: tasks that wait for `main` while other tasks depend on
them. A pure task built over a pending IO task (`Task.map`, `Task.spawn`
reading it) is deferred too, so it does not wait before `main` sets the
flag; asking twice whether such a task has finished, without time passing,
still reports it waiting; `IO.cancel` reaches the tasks that depend on the
canceled one (`mapTask`, `bindTask`), as Lean's task manager propagates it;
a task stored where its type is not statically known (an existential field)
is still the same task for `IO.cancel` and `IO.getTaskState`. -/

structure TPack where
  α : Type
  t : Task α

@[noinline] def mkU (t : Task (Except IO.Error Nat)) : Task Nat :=
  Task.spawn fun _ => match t.get with | .ok v => v + 1 | .error _ => 0

@[noinline] def cancelP (p : TPack) : BaseIO Unit := IO.cancel p.t
@[noinline] def stateP (p : TPack) : BaseIO IO.TaskState := IO.getTaskState p.t

def say (s : String) : BaseIO Unit := (IO.println s).catchExceptions fun _ => pure ()

def main : IO Unit := do
  -- Task.map over a task waiting for main.
  let flag ← IO.mkRef false
  let t ← IO.asTask (do
    while !(← flag.get) do IO.sleep 1
    IO.println "t saw flag"
    return 5)
  let r ← IO.mkRef (Task.pure 0)
  r.set (t.map fun r => match r with | .ok v => v + 1 | .error _ => 0)
  IO.println "main sets flag"
  flag.set true
  IO.println s!"map = {← IO.wait (← r.get)}"
  -- Task.spawn reading a task waiting for main; status queries in between.
  let flag2 ← IO.mkRef false
  let t2 ← IO.asTask (do
    while !(← flag2.get) do IO.sleep 1
    IO.println "t2 saw flag"
    return 6)
  let u := mkU t2
  IO.println s!"u finished? {← IO.hasFinished u}"
  IO.println s!"t2 finished? {← IO.hasFinished t2} {← IO.hasFinished t2}"
  flag2.set true
  IO.println s!"spawn = {← IO.wait u}"
  -- Cancellation reaches dependent tasks.
  let c ← BaseIO.asTask (do IO.sleep 50; return (1 : Nat))
  let m ← BaseIO.mapTask (fun _ => IO.checkCanceled) c
  let b ← BaseIO.bindTask c (fun _ => do let k ← IO.checkCanceled; return Task.pure k)
  IO.cancel c
  IO.println s!"map canceled {← IO.wait m}, bind canceled {← IO.wait b}"
  let m2 ← BaseIO.mapTask (fun _ => IO.checkCanceled) c
  IO.println s!"created after it finished: canceled {← IO.wait m2}"
  -- A task behind an existential field.
  let e ← BaseIO.asTask (do IO.sleep 20; return (← IO.checkCanceled))
  cancelP ⟨Bool, e⟩
  IO.println s!"canceled via pack: {← IO.wait e}"
  let pr ← IO.mkRef (none : Option (BaseIO IO.TaskState))
  let a ← BaseIO.asTask (do
    IO.sleep 10
    match ← pr.get with
    | some q => say s!"own state via pack: {← q}"
    | none => say "no pack"
    return (1 : Nat))
  pr.set (some (stateP ⟨Nat, a⟩))
  IO.println s!"a = {← IO.wait a}"
