/-! Runtime test: specializations made inside `initialize` actions run with
their initializer, after the earlier initializers (natively, right before
the action), so they can read earlier `initialize` constants. -/

@[specialize] def gen {m : Type → Type} [Monad m] (f : Nat → m Nat) : m Nat := f 1

def before : Nat := dbgTrace "before" fun _ => 0

initialize initA : Nat ← do IO.eprintln "initA runs"; pure 41
initialize initS : String ← do IO.eprintln "initS runs"; pure "hello"

-- The specialization reads `initA` and `initS`: it must not run first.
initialize initB : Nat ← do
  IO.eprintln "initB runs"
  pure (Id.run (gen (m := Id) (fun i => dbgTrace "spec in initB" fun _ => pure (i + initA + initS.length))))

def mid : Nat := dbgTrace "mid" fun _ => 1

initialize initR : IO.Ref Nat ← do IO.eprintln "initR runs"; IO.mkRef 17

-- An anonymous `initialize` action.
initialize do
  IO.eprintln "anonymous init runs"
  let v ← initR.get
  IO.eprintln s!"anonymous init sees {Id.run (gen (m := Id) (fun i => dbgTrace "spec in anonymous init" fun _ => pure (i + 100)))} {v}"

builtin_initialize initC : Nat ← do
  IO.eprintln "builtin initC runs"
  pure (Id.run (gen (m := Id) (fun i => dbgTrace "spec in builtin init" fun _ => pure (i + initB))))

def after : Nat := dbgTrace "after" fun _ => 2

def main : IO Unit := do
  IO.println s!"{before} {initA} {initS} {initB} {mid} {← initR.get} {initC} {after}"
