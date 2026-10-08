import Lean
open Lean

/-!
Runtime test: the program of `RtUnreadFieldsData` without the
optimization `unread-fields` (off by default; `RtUnreadFieldsDataOff.opts`
keeps it off also in a run that turns it on for all). The entries' `info`
fields hold `Expr`s that Lean's C++ builds; lean2rr keeps every function
that kept code mentions, so it refuses the program and names those
functions (`RtUnreadFieldsDataOff.refused`). Natively it builds.
-/

structure Entry where
  name : String
  count : Nat
  info : Expr

initialize entriesRef : IO.Ref (Array Entry) ← IO.mkRef #[]

def register (e : Entry) : IO Unit := do
  if (← entriesRef.get).any (·.name == e.name) then
    throw (IO.userError s!"entry {e.name} registered twice")
  entriesRef.modify (·.push e)

initialize
  register { name := "succ3", count := 3, info := mkApp (mkConst ``Nat.succ) (mkNatLit 3) }
  IO.println "registered succ3"

initialize
  register { name := "nat", count := 1, info := mkConst ``Nat [Level.zero] }
  IO.println s!"entries: {(← entriesRef.get).size}"

def main : IO Unit := do
  let es ← entriesRef.get
  IO.println s!"main: {es.map (·.name)}, total {es.foldl (· + ·.count) 0}"
