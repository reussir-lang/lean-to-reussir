/-! Runtime test: `IO.Promise`. A promise's `result?` is a task that
finishes when the promise is resolved (the first resolution counts), with
`none` if the promise is dropped unresolved; its dependents run then (a
`sync` one on the resolving thread). Waiting for an unresolved promise lets
pending tasks run until one resolves it. -/
def ex (x : Except IO.Error Nat) : Nat := x.toOption.getD 999

def stateStr : IO.TaskState → String
  | .waiting => "waiting" | .running => "running" | .finished => "finished"

@[noinline] def resolveLater {α : Type} (p : IO.Promise α) (v : α) : IO (Task (Except IO.Error Unit)) :=
  IO.asTask (do IO.sleep 10; p.resolve v)

def main : IO Unit := do
  -- resolved by main; resolved twice; dependents
  let p ← IO.Promise.new (α := Nat)
  let d ← IO.mapTask (fun (x : Option Nat) => do IO.println s!"dependent {x}"; return 0) p.result?
  let _ ← IO.mapTask (sync := true) (fun (x : Option Nat) => do IO.println s!"sync dependent {x}"; return 0) p.result?
  IO.println s!"resolved? {← p.isResolved} state {stateStr (← IO.getTaskState p.result?)}"
  p.resolve 5
  IO.println "after resolve"
  p.resolve 6
  IO.println s!"resolved? {← p.isResolved} {p.result!.get} {p.result?.get}"
  let _ ← IO.wait d
  -- resolved by a pending task while main waits
  let q ← IO.Promise.new (α := String)
  let _ ← IO.asTask (do IO.sleep 20; q.resolve "from task")
  IO.println s!"waited {q.result!.get}"
  -- through a polymorphic helper (uniform code), and a dependent task
  let q2 ← IO.Promise.new (α := List Nat)
  let _ ← resolveLater q2 [1, 2]
  let m ← IO.mapTask (fun (x : Option (List Nat)) => return x.getD [] |>.length) q2.result?
  IO.println s!"mapped {ex (← IO.wait m)}"
  -- dropped unresolved
  let r ← do
    let p2 ← IO.Promise.new (α := Nat)
    pure p2.result?
  IO.println s!"dropped {r.get}"
  IO.println s!"resultD {(← IO.Promise.new (α := Nat)).resultD 7 |>.get}"
  -- waitAny over an unresolved promise and a pending task
  let q3 ← IO.Promise.new (α := Nat)
  let t ← IO.asTask (do IO.sleep 10; return 3)
  let w ← IO.waitAny [q3.result?.map (fun _ => (.ok 0 : Except IO.Error Nat)), t]
  IO.println s!"waitAny {ex w}"
  q3.resolve 1
