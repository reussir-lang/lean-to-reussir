/-! Runtime test: a closed term that holds tasks waits for them when it is
first evaluated (Lean's `lean_mark_persistent`), with a walk that visits
each cell once and does not recurse, at an 8 MB stack (`RtPersistWalk.pipe`):
a chain of 300000 cells linked through their first field, a DAG of 41
cells reached along 2^40 paths, and a chain of structures linked through
an `Option` field. The same values as constants, which are evaluated at
startup (one of them unused). -/

inductive Chain where
  | nil
  | link (prev : Chain) (job : Task Nat)

@[noinline] def mkChain (n : Nat) (last : Task Nat) : Chain := Id.run do
  let mut c := Chain.nil
  for i in [0:n] do c := .link c (Task.pure i)
  return .link c last

@[noinline] def chainLen : Chain → Nat → Nat
  | .nil, k => k
  | .link p _, k => chainLen p (k + 1)

@[noinline] def lastJob : Chain → Task Nat
  | .link _ t => t
  | .nil => Task.pure 0

inductive T where
  | leaf (t : Task Nat)
  | node (l r : T)

@[noinline] def mk (leaf : Task Nat) : Nat → T
  | 0 => .leaf leaf
  | n + 1 => let s := mk leaf n; .node s s

@[noinline] def leafOf : T → Task Nat
  | .leaf t => t
  | .node l _ => leafOf l

structure Stage where
  prev : Option Stage
  t : Task Nat

@[noinline] def mkStages (n : Nat) (last : Task Nat) : Stage := Id.run do
  let mut s : Stage := { prev := none, t := Task.pure 0 }
  for i in [1:n] do s := { prev := some s, t := Task.pure i }
  return { prev := some s, t := last }

@[noinline] partial def stageCount : Option Stage → Nat → Nat
  | none, k => k
  | some s, k => stageCount s.prev (k + 1)

def stateStr : IO.TaskState → String
  | .waiting => "waiting" | .running => "running" | .finished => "finished"

-- Constants: evaluated at startup.
def chainC : Chain := mkChain 300000 (Task.pure 5)
def dagC : T := mk (Task.pure 1) 40
def stagesC : Stage := mkStages 300000 (Task.pure 9)

def main : IO Unit := do
  IO.println s!"constants: {chainLen chainC 0} {(lastJob chainC).get} {(leafOf dagC).get}"
  -- A task still running: the closed terms below are walked.
  let busy ← IO.asTask (do IO.sleep 50; return 1)
  let c := mkChain 300000 (Task.spawn fun _ => dbgTrace "chain task runs" fun _ => (7 : Nat))
  IO.println s!"chain: {stateStr (← IO.getTaskState (lastJob c))} {chainLen c 0}"
  let d := mk (Task.spawn fun _ => dbgTrace "dag task runs" fun _ => (11 : Nat)) 40
  IO.println s!"dag: {stateStr (← IO.getTaskState (leafOf d))}"
  let s := mkStages 300000 (Task.spawn fun _ => dbgTrace "stage task runs" fun _ => (13 : Nat))
  IO.println s!"stages: {stateStr (← IO.getTaskState s.t)} {stageCount (some s) 0}"
  let _ ← IO.wait busy
  IO.println s!"values: {(lastJob c).get} {(leafOf d).get} {s.t.get}"
