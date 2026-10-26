/-! Runtime test (review of the shared drop stack, its leanrt side): promise
dependents that run at the end of a drain (the end work) free trees
holding promises and wait for tasks: a task finished before, one not
finished (it sleeps first), a dedicated one, two promises in one tree, and
a dependent that frees an array of trees. Each task frees a tree holding
its own promise `q` and waits for `q`'s result. `Tr` has two recursive
fields, so Reussir frees it through the stack of pending drops. With a drop
stack of Reussir's own beside leanrt's, the dependents ran inside
Reussir's drain and their frees joined it: the tasks waited for good (the
`.pipe` stops the program after 20 s and prints the exit code; stderr,
where Lean warns that `Task.get` is called from a `sync` task, is not
compared). See also RtPromiseDepWaitInDrain. -/
inductive Tr where
  | leaf : Tr
  | node : Tr → Option (IO.Promise Unit) → Tr → Tr

def Tr.size : Tr → Nat
  | .leaf => 0
  | .node l _ r => l.size + 1 + r.size

@[noinline] def consume (tag : String) (t : Tr) : IO Unit := do
  IO.println s!"{tag} size {t.size}"

@[noinline] def consumeArr (tag : String) (ts : Array Tr) : IO Unit := do
  IO.println s!"{tag} arr {ts.size}"

def deep (p : IO.Promise Unit) : Tr := .node .leaf none (.node .leaf none (.node .leaf (some p) .leaf))

@[noinline] def taskBody (name : String) : IO String := do
  let q ← IO.Promise.new (α := Unit)
  let r := q.result?
  consume name (deep q)
  match ← IO.wait r with
  | none => pure s!"{name}: q dropped"
  | some _ => pure s!"{name}: q resolved"

def waitDep (name : String) (tB : Task (Except IO.Error String)) (p : IO.Promise Unit) : BaseIO (Task (Except IO.Error Unit)) :=
  IO.mapTask (sync := true) (fun (_ : Option Unit) => do
      IO.println s!"{name} start"
      let v ← IO.ofExcept (← IO.wait tB)
      IO.println s!"{name} got [{v}]") p.result?

def s1 : IO Unit := do
  let tB ← IO.asTask (taskBody "B1")
  let v ← IO.wait tB
  IO.println s!"s1 B finished first: {v.toOption}"
  let pA ← IO.Promise.new (α := Unit)
  let d ← waitDep "dep1" tB pA
  consume "s1" (deep pA)
  let _ ← IO.wait d
  IO.println "s1 done"

def s2 : IO Unit := do
  let tB ← IO.asTask (do IO.sleep 30; taskBody "B2")
  let pA ← IO.Promise.new (α := Unit)
  let d ← waitDep "dep2" tB pA
  consume "s2" (deep pA)
  let _ ← IO.wait d
  IO.println "s2 done"

def s3 : IO Unit := do
  let tB ← IO.asTask (taskBody "B3") (prio := .dedicated)
  let pA ← IO.Promise.new (α := Unit)
  let d ← waitDep "dep3" tB pA
  consume "s3" (deep pA)
  let _ ← IO.wait d
  IO.println "s3 done"

def s4 : IO Unit := do
  let tB ← IO.asTask (do IO.sleep 30; taskBody "B4")
  let pA ← IO.Promise.new (α := Unit)
  let pB ← IO.Promise.new (α := Unit)
  let dA ← waitDep "dep4a" tB pA
  let dB ← IO.mapTask (sync := true) (fun (_ : Option Unit) => IO.println "dep4b ran") pB.result?
  consume "s4" (.node (.node .leaf (some pA) .leaf) none (.node .leaf (some pB) .leaf))
  let _ ← IO.wait dA
  let _ ← IO.wait dB
  IO.println "s4 done"

def s5 : IO Unit := do
  let pA ← IO.Promise.new (α := Unit)
  let d ← IO.mapTask (sync := true) (fun (_ : Option Unit) => do
      IO.println "dep5 start"
      let q1 ← IO.Promise.new (α := Unit)
      let q2 ← IO.Promise.new (α := Unit)
      let r1 := q1.result?
      let r2 := q2.result?
      consumeArr "dep5" #[deep q1, .leaf, deep q2]
      IO.println s!"dep5 q1 {← IO.hasFinished r1} q2 {← IO.hasFinished r2}"
      let t ← IO.asTask (taskBody "B5")
      let v ← IO.ofExcept (← IO.wait t)
      IO.println s!"dep5 got [{v}]") pA.result?
  consume "s5" (deep pA)
  let _ ← IO.wait d
  IO.println "s5 done"

def main : IO Unit := do
  s1; s2; s3; s4; s5
  IO.println "main: done"
