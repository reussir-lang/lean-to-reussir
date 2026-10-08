/-! Runtime test (hunt HTG-01): a dedicated task whose last reference goes
while it runs wakes no waiter when it finishes. Natively an IO task holds a
reference to itself while it runs (`keep_alive`); once the program's
reference is gone, that reference is the last, and its release when the
task's closure returns deletes the task (`m_deleted`), which is freed
without `resolve_core`'s `notify_all`. Here `p.resolve 1` runs `slow`, a
`sync` dependent of `p`'s task that sleeps 2.5 s, so `p`'s waiters wake only
at the end of that walk or at the next notification; the dedicated task `w`
blocked in `IO.waitAny [r]` wakes at the referenced task `o`'s finish (about
1.6 s), not at the dropped task `u`'s (about 0.7 s). Natively, on stderr:
"dropped task finishes", "referenced task finishes", then "waitAny woke".

leanrt ended a dedicated task inside its job (lean-runtime's
`end_running_task`) before the job's reference to the cell went, so the
task was released only after lean-runtime had ended it, and its finish woke
`w`: "waitAny woke" came before "referenced task finishes". Since then the
job's reference goes before lean-runtime ends the task, as for a pool task.
The sleeps leave margins of about 0.9 s. -/

def main : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  let r := p.result?
  let slow ← IO.mapTask (sync := true) (fun _ => do IO.sleep 2500; IO.eprintln "slow sync dep done") r
  let ready ← IO.Promise.new (α := Unit)
  let w ← IO.asTask (prio := .dedicated) do
    ready.resolve ()
    let v ← IO.waitAny [r]
    IO.eprintln s!"waitAny woke: {repr v}"
  let _ ← IO.wait ready.result?
  IO.sleep 100
  let u ← IO.asTask (prio := .dedicated) do
    IO.sleep 500
    IO.eprintln "dropped task finishes"
  let o ← IO.asTask (prio := .dedicated) do
    IO.sleep 1400
    IO.eprintln "referenced task finishes"
  IO.sleep 100
  -- the last use of `u`: its reference goes here, while it sleeps
  let st ← IO.getTaskState u
  IO.eprintln s!"u is {st}"
  IO.eprintln "resolving"
  p.resolve 1
  IO.eprintln "resolved"
  let _ ← IO.wait w
  let _ ← IO.wait slow
  let _ ← IO.wait o
