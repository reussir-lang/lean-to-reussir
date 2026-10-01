/-! Runtime test: polling for tasks that run on other threads (contexts
here): `IO.hasFinished` in a busy loop for a sleeping task, `IO.getTaskState`
for a task blocked on a promise a sleeping task resolves, a loop polling a
reference with `IO.sleep 0`; a dependent of a task that is blocked, waited
for (it runs when its source finishes, with its cancellation) and asked
about (it is waiting). -/
def eStr {α} [ToString α] : Except IO.Error α → String
  | .ok v => toString v
  | .error e => s!"error {e}"

def stateStr : IO.TaskState → String
  | .waiting => "waiting" | .running => "running" | .finished => "finished"

def main : IO Unit := do
  let t ← IO.asTask (do IO.sleep 100; return (1 : Nat))
  IO.sleep 20
  let mut n := 0
  while !(← IO.hasFinished t) do
    n := n + 1
  IO.println s!"finished after polling: {decide (n > 0)} {eStr (← IO.wait t)}"
  let p ← IO.Promise.new (α := Nat)
  let w ← IO.asTask (do return (← IO.wait p.result!) + 1)
  let _r ← IO.asTask (do IO.sleep 80; p.resolve 1)
  IO.sleep 20
  let mut m := 0
  while (← IO.getTaskState w) != .finished do
    m := m + 1
  IO.println s!"blocked task finished after polling: {decide (m > 0)} {eStr (← IO.wait w)}"
  let flag ← IO.mkRef false
  let _t ← IO.asTask (do IO.sleep 50; flag.set true)
  let mut k := 0
  while !(← flag.get) do
    IO.sleep 0
    k := k + 1
  IO.println s!"flag seen after polling with sleep 0: {decide (k > 0)}"
  -- a dependent of a blocked task, waited for
  let q ← IO.Promise.new (α := Nat)
  let w2 ← IO.asTask (do return (← IO.wait q.result!))
  IO.sleep 10
  let dep ← IO.mapTask (fun r => do return s!"{eStr r} canceled={← IO.checkCanceled}") w2
  IO.cancel w2
  let _ ← IO.asTask (do IO.sleep 30; q.resolve 4)
  IO.println s!"dependent waited for: {eStr (← IO.wait dep)}"
  -- its state while a task waits for it
  let q3 ← IO.Promise.new (α := Nat)
  let w3 ← IO.asTask (do return (← IO.wait q3.result!))
  IO.sleep 10
  let dep3 ← IO.mapTask (fun r => do return (match r with | .ok v => v + 1 | .error _ => 0)) w3
  let waiter ← IO.asTask (do return (← IO.wait dep3))
  IO.sleep 20
  IO.println s!"dependent while its source is blocked: {stateStr (← IO.getTaskState dep3)}"
  IO.println s!"its waiter: {stateStr (← IO.getTaskState waiter)}"
  q3.resolve 5
  IO.println s!"values {eStr (← IO.wait waiter)} {eStr (← IO.wait dep3)}"
