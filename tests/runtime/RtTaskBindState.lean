/-! Runtime test: a bind task (`IO.bindTask`) whose function has returned an
unfinished task waits for it, and reports `waiting` meanwhile (natively its
closure is set again); while its function runs it is `running`. -/
def ex (x : Except IO.Error Nat) : Nat := x.toOption.getD 999

def stateStr : IO.TaskState → String
  | .waiting => "waiting" | .running => "running" | .finished => "finished"

def main : IO Unit := do
  let bref ← IO.mkRef (Task.pure (.ok 0) : Task (Except IO.Error Nat))
  let src ← IO.asTask (do IO.sleep 30; return 1)
  let b ← IO.bindTask src (fun x => do
    IO.println s!"in f, bind task {stateStr (← IO.getTaskState (← bref.get))}"
    IO.asTask (do
      IO.sleep 10
      IO.println s!"in continuation, bind task {stateStr (← IO.getTaskState (← bref.get))}"
      return ex x + 1))
  bref.set b
  IO.println s!"result {ex (← IO.wait b)} {stateStr (← IO.getTaskState b)}"
