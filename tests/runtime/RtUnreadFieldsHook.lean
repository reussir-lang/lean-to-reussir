import Lean
open Lean

/-!
Runtime test of the optimization `unread-fields` (off by default; this
test turns it on, `RtUnreadFieldsHook.enable-opts`). An `initialize` block
registers a hook, a structure with a function field, in an `IO.Ref`. The
program reads the hooks' names (the duplicate check) but never their `run`
field, so no kept code can call a hook. The callback calls
`Lean.Expr.dbgToString`, a C++ function of the `Lean` package that
lean2rr's runtime does not have: with the pass, the callback, the
`validate` argument that the closure in `registerHook` captures, and the
caller's lambda are left out, and the program equals native (the
initializer's output included). The second callback also reads
`Lean.manualRoot`, an `initialize` constant of the `Lean` package whose
initializer calls another C++ function (`lean_manual_get_root`): once no
kept code reads the constant, its startup step does not run either.
Without the pass lean2rr refuses the program (`RtUnreadFieldsHookOff`, the
same program).
-/

structure Hook where
  name : String
  run : Expr → String

initialize hooksRef : IO.Ref (Array Hook) ← IO.mkRef #[]

def registerHook (name : String) (validate : Expr → String) : IO Unit := do
  if (← hooksRef.get).any (·.name == name) then
    throw (IO.userError s!"hook {name} registered twice")
  hooksRef.modify (·.push { name, run := fun e => validate e ++ "!" })

initialize
  registerHook "dbg" (fun e => e.dbgToString)
  IO.println "registered dbg"

initialize
  registerHook "dbg2" (fun e => s!"[{e.dbgToString}] see {manualRoot}")
  IO.println s!"hooks: {(← hooksRef.get).size}"

def main : IO Unit := do
  let hs ← hooksRef.get
  IO.println s!"main: {hs.size} hooks, names {hs.map (·.name)}"
