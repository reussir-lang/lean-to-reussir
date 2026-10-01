/-! Runtime test: promises resolved by tasks that run while the program
waits or polls; promises in a list handled by polymorphic code; the
dependents of a promise resolved inside a task; a canceled promise. -/
def stateStr : IO.TaskState → String
  | .waiting => "waiting" | .running => "running" | .finished => "finished"

@[noinline] def resolveAll {α : Type} (ps : List (IO.Promise α)) (v : α) : BaseIO Unit :=
  ps.forM fun p => p.resolve v

def main : IO Unit := do
  -- polled with isResolved while a task resolves it
  let p ← IO.Promise.new (α := Nat)
  let _ ← IO.asTask (do IO.sleep 20; p.resolve 9)
  let mut n := 0
  while !(← p.isResolved) do
    IO.sleep 5
    n := n + 1
  IO.println s!"polled {decide (n > 0)} {p.result!.get}"
  -- resolved by a dependent of a pending task
  let q ← IO.Promise.new (α := String)
  let src ← IO.asTask (do IO.sleep 10; return "from dependent")
  let _ ← IO.mapTask (fun r => q.resolve (r.toOption.getD "?")) src
  IO.println s!"waited {(← IO.wait q.result?).getD "none"}"
  -- a list of promises, resolved by polymorphic code in a task
  let ps ← (List.range 3).mapM fun _ => IO.Promise.new (α := Nat × String)
  let deps ← ps.mapM fun p => IO.mapTask (fun (x : Option (Nat × String)) => return x.map (·.1)) p.result?
  let _ ← IO.asTask (resolveAll ps (4, "four"))
  let vs ← deps.mapM fun d => return (← IO.wait d).toOption.join
  IO.println s!"list {vs} {ps.map (·.result!.get.2)}"
  -- canceled before it is resolved: its dependents are canceled
  let c ← IO.Promise.new (α := Nat)
  let cd ← IO.mapTask (fun (_ : Option Nat) => do return (← IO.checkCanceled)) c.result?
  IO.cancel c.result?
  IO.println s!"before resolve {stateStr (← IO.getTaskState c.result?)} {stateStr (← IO.getTaskState cd)}"
  c.resolve 1
  IO.println s!"dependent canceled {(← IO.wait cd).toOption} {c.result!.get}"
