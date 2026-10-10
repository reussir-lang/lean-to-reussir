/-! Runtime test: `Runtime.markPersistent` of a value that reaches an
unresolved promise waits until the promise is resolved, as native
`lean_mark_persistent` (it pushes the promise's result task, then calls
`lean_task_get` on that task): a promise itself, a promise in a
structure, and a promise at a type parameter (hunt HTSK2-02). Before the
fix the walk did not look into a promise: "after markPersistent" came
before the resolving task's output. -/
structure Holder where
  name : String
  prom : IO.Promise Nat

/-- At the structure's own type. -/
@[noinline] unsafe def markHolder (h : Holder) : IO Holder := Runtime.markPersistent h

/-- At a type parameter: the argument is a `Box`. -/
@[noinline] unsafe def markGen {α : Type} (x : α) : IO α := Runtime.markPersistent x

/-- Resolve `p` with `v` after `ms` milliseconds, on a dedicated thread. -/
def resolveLater (tag : String) (p : IO.Promise Nat) (ms : UInt32) (v : Nat) : IO Unit := do
  let _ ← IO.asTask (prio := .dedicated) do
    IO.sleep ms
    IO.println s!"{tag}: resolving"
    p.resolve v

def main : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  resolveLater "direct" p 200 5
  let p' ← unsafe Runtime.markPersistent p
  IO.println "after markPersistent of a promise"
  let q ← IO.Promise.new (α := Nat)
  resolveLater "packed" q 200 6
  let h ← unsafe markHolder { name := "h", prom := q }
  IO.println s!"after markPersistent of a structure ({h.name})"
  let g ← IO.Promise.new (α := Nat)
  resolveLater "generic" g 200 7
  let g' ← unsafe markGen g
  IO.println "after markPersistent at a type parameter"
  -- A resolved promise: its value is there, nothing to wait for.
  let d ← unsafe Runtime.markPersistent p'
  IO.println s!"{p'.result?.get} {h.prom.result?.get} {g'.result?.get} {d.result?.get}"
