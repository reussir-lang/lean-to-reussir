/-! Runtime test: a promise passed to a function that borrows it is
released by the caller after the call (plan §5.8, "Borrowing"). The last
reference to an unresolved promise resolves its `result?` task with
`none`, so its release time shows: natively the task is not finished while
the callee runs. lean2rr counted only files and child processes as
resources (`resourceExterns`): a program that made promises but no files
got Reussir's release times, and the promise was released at its last use
inside the callee (hunt3 own, `finished inside: true`).
- `check p`: the callee reads the promise only through `result?` (which
  borrows it), then asks whether that task has finished;
- the same through a function value (natively Lean's `_boxed` releases the
  promise after the call);
- `checkPair s`: a structure holding the promise, lent to the callee;
- after each call the caller has dropped the promise: a dependent task
  made before the call sees `none`. -/

@[noinline] def check (p : IO.Promise Nat) : IO Bool := do
  let t := p.result?
  IO.hasFinished t

@[noinline] def applyTo (f : IO.Promise Nat → IO Bool) (p : IO.Promise Nat) : IO Bool := f p

structure PP where
  p : IO.Promise Nat
  n : Nat

@[noinline] def checkPair (s : PP) : IO Bool := do
  IO.hasFinished s.p.result?

def after (t : Task (Except IO.Error Nat)) : IO Unit := do
  match ← IO.wait t with
  | .ok v => IO.println s!"after: {v}"
  | .error e => IO.println s!"after: error {e}"

def main : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  let t ← IO.mapTask (fun o => pure (o.getD 7)) p.result? (sync := true)
  IO.println s!"direct: finished inside {← check p}"
  after t
  let q ← IO.Promise.new (α := Nat)
  let tq ← IO.mapTask (fun o => pure (o.getD 8)) q.result? (sync := true)
  IO.println s!"function value: finished inside {← applyTo (fun p => check p) q}"
  after tq
  let r ← IO.Promise.new (α := Nat)
  let tr ← IO.mapTask (fun o => pure (o.getD 9)) r.result? (sync := true)
  IO.println s!"structure: finished inside {← checkPair ⟨r, 1⟩}"
  after tr
