import Lean
open Lean

/-!
Runtime test of the optimization `unread-fields` (off by default; this
test turns it on, `RtUnreadFieldsData.enable-opts`): data in a field that
no kept code reads. An `initialize` block registers entries whose `info`
is an `Expr`, which Lean's C++ builds (`Lean.Expr.mkData`,
`Lean.Expr.mkAppData`, `Lean.Level.mkData`); the program reads the
entries' names and counts but never `info`. With the pass the `Expr`s
and the code that builds them are left out, and the program equals
native, the initializers' output included. Without the pass lean2rr
refuses it (`RtUnreadFieldsDataOff`, the same program).
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
