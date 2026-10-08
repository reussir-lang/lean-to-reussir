/-!
Runtime test of the optimization `unread-fields` (off by default; this
test turns it on, `RtUnreadFieldsStartup.enable-opts`): the `initialize`
blocks still run, in native order, with their output and their errors,
when the callbacks they register are left out. Hooks are registered with
a duplicate check that reads their names; their `run` fields are never
read. A callback made by an IO action (`mkRun`, which prints) comes back
in the action's result, whose field is read, so it is kept and `mkRun`
still prints; a lambda passed directly is left out. The third block
registers a name twice: natively the program stops at startup with the
uncaught exception and exit code 1, before `main`.
-/

structure Hook where
  name : String
  run : Nat → IO Unit

initialize hooksRef : IO.Ref (Array Hook) ← IO.mkRef #[]

def mkRun (tag : String) : IO (Nat → IO Unit) := do
  IO.println s!"making {tag}"
  return fun n => IO.println s!"{tag} {n}"

def registerHook (name : String) (run : Nat → IO Unit) : IO Unit := do
  if (← hooksRef.get).any (·.name == name) then
    throw (IO.userError s!"hook {name} registered twice")
  IO.println s!"registering {name}"
  hooksRef.modify (·.push { name, run })

initialize do
  registerHook "a" (← mkRun "a")
  IO.eprintln "stderr after a"

initialize do
  registerHook "b" (fun n => IO.println s!"b {n}")
  IO.println s!"hooks: {(← hooksRef.get).map (·.name)}"

initialize do
  registerHook "c" (← mkRun "c")
  registerHook "a" (fun n => IO.println s!"a again {n}")
  IO.println "not reached"

def main : IO Unit := IO.println "main (not reached)"
