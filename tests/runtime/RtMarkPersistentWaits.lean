/-! Runtime test: `Runtime.markPersistent` waits for the tasks its value
reaches, as a constant's first evaluation does (natively
`lean_mark_persistent` calls `lean_task_get` on each task object it
reaches); a thunk it reaches is not forced. Before the fix lean2rr's
primitive was the identity: "after markPersistent" came before the task's
output. -/
structure Pack where
  job : Task (Except IO.Error Nat)
  lazy : Thunk Nat

def job (tag : String) (ms : UInt32) (v : Nat) : IO Nat := do
  IO.sleep ms
  IO.println s!"{tag} done"
  pure v

/-- At a type parameter: the argument is a `Box`. -/
@[noinline] unsafe def markGen {α : Type} (x : α) : IO α := Runtime.markPersistent x

def main : IO Unit := do
  let t ← IO.asTask (job "direct" 100 5)
  let t' ← unsafe Runtime.markPersistent t
  IO.println "after markPersistent of a task"
  let p : Pack := { job := ← IO.asTask (job "packed" 100 6),
                    lazy := Thunk.mk fun _ => dbgTrace "thunk forced" fun _ => 7 }
  let p' ← unsafe Runtime.markPersistent p
  IO.println "after markPersistent of a structure"
  let g ← unsafe markGen (← IO.asTask (job "generic" 100 8))
  IO.println "after markPersistent at a type parameter"
  let l ← unsafe Runtime.markPersistent [1, 2, 3]
  IO.println s!"{l}"
  let r1 ← IO.wait t'
  let r2 ← IO.wait p'.job
  let r3 ← IO.wait g
  IO.println s!"{r1.toOption} {r2.toOption} {r3.toOption} {p'.lazy.get}"
