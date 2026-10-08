/-! Runtime test: a closed term that only another closed term reads (one
use, so lean2rr evaluates it where it is used instead of in a once-cell,
`chainConsts`) and whose value holds tasks waits for them when it is first
evaluated: natively `lean_obj_once_cold` marks it persistent
(`lean_mark_persistent`, which calls `lean_task_get` on each task), and
keeps it. Here `count`'s closed term `List.length (spawnOne 7)` reads the
closed term `spawnOne 7`, and `many`'s list literal `[mk 1, mk 2]` is a
chain of closed terms. Before the fix such a term had no walk and was not
kept: its tasks were dropped and never ran (no "task … runs" line). -/
@[noinline] def spawnOne (n : Nat) : List (Task Nat) :=
  [Task.spawn fun _ => dbgTrace s!"task {n} runs" fun _ => n]

@[noinline] def count (u : Unit) : Nat := (spawnOne 7).length

@[noinline] def mk (n : Nat) : Task Nat :=
  dbgTrace s!"spawn {n}" fun _ => Task.spawn fun _ => dbgTrace s!"task {n} runs" fun _ => n

@[noinline] def many (u : Unit) : Nat := [mk 1, mk 2].length

def main : IO Unit := do
  IO.eprintln "before"
  IO.eprintln s!"count {count ()}"
  IO.eprintln s!"many {many ()}"
  IO.eprintln "after"
