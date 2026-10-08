/-!
Runtime test of the optimization `unread-fields` (off by default; this
test turns it on, `RtUnreadFieldsCalled.enable-opts`): callbacks that
`initialize` blocks register and that `main` reads and calls are kept.
`main` reads the field `run` by projection (`h.run`), by a match on the
structure (`⟨_, r, _⟩`) and through a callback stored inside another
structure's field (`Hook.wrap`, a field holding a structure that holds a
function); a callback is also captured by a closure that a registration
function builds from its parameter (`registerHook`'s `validate`).
-/

structure Inner where
  call : Nat → String

structure Hook where
  name : String
  run : Nat → String
  wrap : Inner

initialize hooksRef : IO.Ref (Array Hook) ← IO.mkRef #[]

def registerHook (name : String) (validate : Nat → String) : IO Unit := do
  if (← hooksRef.get).any (·.name == name) then
    throw (IO.userError s!"hook {name} registered twice")
  hooksRef.modify (·.push { name, run := fun n => validate n ++ "!",
                            wrap := { call := fun n => s!"{name} wraps {validate (n + 1)}" } })

initialize registerHook "double" (fun n => toString (2 * n))
initialize registerHook "square" (fun n => toString (n * n))

def main (args : List String) : IO Unit := do
  let k := args.length + 7
  for h in (← hooksRef.get) do
    IO.println s!"{h.name}: {h.run k}"
  for h in (← hooksRef.get) do
    match h with
    | ⟨n, r, _⟩ => IO.println s!"{n} matched: {r 3}"
  for h in (← hooksRef.get) do
    IO.println (h.wrap.call 10)
