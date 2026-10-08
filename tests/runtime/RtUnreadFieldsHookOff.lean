import Lean
open Lean

/-!
Runtime test: the program of `RtUnreadFieldsHook` with lean2rr's default
passes, so without the optimization `unread-fields` (off by default). The
hooks' callbacks call `Lean.Expr.dbgToString`, a C++ function of the
`Lean` package that lean2rr's runtime does not have; lean2rr keeps every
function that kept code mentions, so it refuses the program and names the
functions (`RtUnreadFieldsHookOff.refused`; the second callback's
`Lean.manualRoot` adds `lean_manual_get_root`, which its initializer
calls). Natively it builds.
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
