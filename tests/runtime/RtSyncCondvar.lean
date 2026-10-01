import Std.Sync
/-! Runtime test: `Std.Condvar` and `Std.Barrier` between tasks (threads of
their own natively). Two tasks take turns through a mutex and a condition
variable (each waits until it is its turn, so the prints alternate); a task
waits (`atomicallyOnce`) for a counter another task raises; a barrier lets
three tasks through together, one of them the leader, twice; `notifyOne`
wakes one waiter at a time. -/
open Std

def player (m : Mutex Nat) (cv : Condvar) (me : Nat) (rounds : Nat) (log : IO.Ref (Array String)) : IO Unit := do
  for i in [0:rounds] do
    m.atomicallyOnce cv (do return (← get) % 2 == me) do
      log.modify (·.push s!"player {me} round {i}")
      modify (· + 1)
    cv.notifyAll

def main : IO Unit := do
  -- turn taking
  let m ← Mutex.new 0
  let cv ← Condvar.new
  let log ← IO.mkRef #[]
  let a ← IO.asTask (prio := .dedicated) (player m cv 0 5 log)
  let b ← IO.asTask (prio := .dedicated) (player m cv 1 5 log)
  IO.ofExcept (← IO.wait a)
  IO.ofExcept (← IO.wait b)
  for l in ← log.get do IO.println l
  -- waiting for a counter
  let c ← Mutex.new 0
  let cv2 ← Condvar.new
  let waiter ← IO.asTask (prio := .dedicated) do
    c.atomicallyOnce cv2 (do return (← get) ≥ 100) do
      return (← get)
  let _ ← IO.asTask (prio := .dedicated) do
    for _ in [0:100] do
      c.atomically (modify (· + 1))
      cv2.notifyOne
  IO.println s!"waiter saw {← IO.ofExcept (← IO.wait waiter)}"
  -- a barrier, used twice
  let bar ← Barrier.new 3
  let arrived ← IO.mkRef (0 : Nat)
  for round in [0:2] do
    let ts ← (List.range 3).mapM fun _ => IO.asTask (prio := .dedicated) do
      arrived.modify (· + 1)
      let leader ← bar.wait
      return (leader, ← arrived.get)
    let rs ← ts.mapM fun t => do IO.ofExcept (← IO.wait t)
    let leaders := rs.filter (·.1) |>.length
    IO.println s!"round {round}: {leaders} leader, all saw {rs.all (·.2 == 3 * (round + 1))}"
  -- notifyOne: one waiter per notification
  let n ← Mutex.new (0 : Nat)
  let cv3 ← Condvar.new
  let go ← IO.mkRef (0 : Nat)
  let waiters ← (List.range 3).mapM fun i => IO.asTask (prio := .dedicated) do
    n.atomically do
      modify (· + 1)
      cv3.waitUntil n.mutex (do return (← go.get) > i)
    return i
  -- all three are waiting once the count is 3
  while (← n.atomically get) < 3 do IO.sleep 1
  for k in [1:4] do
    n.atomically do go.set k
    cv3.notifyAll
  for t in waiters do IO.println s!"waiter {← IO.ofExcept (← IO.wait t)} done"
