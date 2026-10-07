/-! Runtime test (with one native worker thread, `NAME.pipe`; the priorities
come from `NAME.args`): a task priority above `Task.Priority.max` (8) makes a
dedicated task, whatever its size (Init/Core.lean: "Tasks with a priority
greater than `Task.Priority.max` are scheduled on dedicated threads"). Each
spawner makes a task at the priority under test while the one pool worker
runs `busy`, which polls until the promise `free` is resolved. A dedicated
task runs while the worker is busy and frees it; a pool task waits in the
queue until a rescuer frees the worker after a second. `IO.asTask`,
`IO.mapTask` and `IO.bindTask` check and free in the task itself;
`Task.spawn`, `Task.map` and `Task.bind` make a pure task, and a dedicated
`IO.mapTask` of it checks and frees once it has finished.

lean2rr passes the whole priority to lean-runtime, a `Nat` of 2^64 or more
as `u64::MAX` (lean-runtime's LB-39): at 2^32 + 1 and at 2^64 every task is
dedicated. Natively Lean cuts the priority to a C `unsigned`: 2^32 + 1 is
priority 1, a pool task; for 2^64, a big `Nat`, it takes the bits of the
object's pointer, which in practice are above 8 (a dedicated task by
chance). So the outputs differ at 2^32 + 1 (`NAME.l2r.out`,
`NAME.native.out`). Before lean2rr passed the whole priority, a dependent
(`Task.map`, `Task.bind`, `IO.mapTask`, `IO.bindTask`) kept its priority as
32 bits, so 2^32 + 1 was a pool task, and 2^64 was priority 0 for every
spawner. -/

def seen (r : Option String) : String :=
  match r with
  | some s => s
  | none => "dropped"

/-- A dedicated task that resolves `p` with "rescuer" after a second. -/
def rescue (p : IO.Promise String) : IO Unit := do
  let _ ← IO.asTask (prio := .dedicated) (do IO.sleep 1000; p.resolve "rescuer")

/-- `spawn done free` makes the task at the priority under test while the one
pool worker runs `busy`, which polls until `free` is resolved, then resolves
`done`. -/
def busyCase (label : String)
    (spawn : IO.Promise Unit → IO.Promise String → BaseIO (Task (Except IO.Error Bool))) :
    IO Unit := do
  let free ← IO.Promise.new
  let started ← IO.Promise.new
  let done ← IO.Promise.new
  let busy ← IO.asTask (do
    started.resolve ()
    while !(← IO.hasFinished free.result?) do IO.sleep 10
    done.resolve ())
  let _ ← IO.wait started.result?
  rescue free
  let t ← spawn done free
  match ← IO.wait t with
  | .ok b => IO.println s!"{label}: the task ran while the worker was busy: {b}"
  | .error e => IO.println s!"{label}: error {e}"
  IO.println s!"{label}: the worker was freed by {seen (← IO.wait free.result?)}"
  let _ ← IO.wait busy

/-- Whether `busy` still runs; then the worker is freed. -/
def check (done : IO.Promise Unit) (free : IO.Promise String) : IO Bool := do
  let ranWhileBusy := !(← IO.hasFinished done.result?)
  free.resolve "the task"
  return ranWhileBusy

/-- The check of a pure task `t`: a dedicated `IO.mapTask` of it. -/
def checkAfter (t : Task α) (done : IO.Promise Unit) (free : IO.Promise String) :
    BaseIO (Task (Except IO.Error Bool)) :=
  IO.mapTask (prio := .dedicated) (fun _ => check done free) t

def run (a : String) : IO Unit := do
  let p := a.toNat!
  busyCase s!"asTask {a}" fun done free => IO.asTask (prio := p) (check done free)
  busyCase s!"mapTask {a}" fun done free =>
    IO.mapTask (prio := p) (fun _ => check done free) (Task.pure p)
  busyCase s!"bindTask {a}" fun done free =>
    IO.bindTask (prio := p) (Task.pure p) fun _ => do
      let b ← check done free
      return Task.pure (.ok b)
  -- The pure task's value comes from an action of the spawner, so the task
  -- is made there.
  busyCase s!"Task.spawn {a}" fun done free => do
    let d ← IO.hasFinished done.result?
    checkAfter (Task.spawn (prio := p) fun _ => !d) done free
  busyCase s!"Task.map {a}" fun done free => do
    let d ← IO.hasFinished done.result?
    checkAfter ((Task.pure d).map (prio := p) fun x => !x) done free
  busyCase s!"Task.bind {a}" fun done free => do
    let d ← IO.hasFinished done.result?
    checkAfter ((Task.pure d).bind (prio := p) fun x => Task.pure !x) done free

def main (args : List String) : IO Unit := do
  for a in args do run a
