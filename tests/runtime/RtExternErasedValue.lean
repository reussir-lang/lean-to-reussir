/-! Runtime test: thunk and task externs whose value is erased in compiled
code. `Task.pure`, `Thunk.pure` and `Task.spawn` are polymorphic in a
universe, so their value can be a type (`α := Type`) or a proposition
(`α := Prop`); mono code erases it (`◾`). lean2rr's glue for these externs
reads its arguments by position, and dropped the erased value: the
translation failed (`index out of bounds`, then a type error in rrc). The
values carry nothing, so the program only shows that the tasks and thunks
exist and that a computation the instance erases (a function whose result
is a type or a proposition) never runs: natively its closure is `box(0)`,
and applying `box(0)` gives `box(0)`. -/

@[noinline] def mkT (n : Nat) : Task Type := if n > 3 then Task.pure Nat else Task.pure String
@[noinline] def mkTh (n : Nat) : Thunk Type := if n > 3 then Thunk.pure Nat else Thunk.pure String
@[noinline] def mkP (n : Nat) : Task Prop := Task.pure (n = 2)
@[noinline] def mkThP (n : Nat) : Thunk Prop := Thunk.mk fun _ => dbgTrace s!"thunk {n}" fun _ => n = 3
@[noinline] def spawnT (n : Nat) : Task Type :=
  Task.spawn fun _ => dbgTrace s!"spawn {n}" fun _ => if n > 3 then Nat else Bool
-- A partial application of the extern: the erased value is its last
-- argument.
@[noinline] def pures (n : Nat) : List (Task Prop) := [n = 1, n = 2].map Task.pure
@[noinline] def mapT (t : Task Type) : Task Nat := t.map fun _ => 7
-- A function whose result is a type: erased, so its body never runs.
@[noinline] def mapE (t : Task Nat) : Task Type :=
  t.map fun n => dbgTrace s!"map {n}" fun _ => if n > 3 then Nat else Bool

-- `ptrAddrUnsafe` of a type: natively the address of `box(0)`, 1 (lean2rr
-- had no glue for it: the program was refused).
unsafe def addrTy (a : Type) : USize := ptrAddrUnsafe a
@[implemented_by addrTy] def addrTy' (_ : Type) : USize := 0

def main (args : List String) : IO Unit := do
  let n := args.length
  IO.println s!"task {← IO.hasFinished (mkT n)}"
  let _ := (mkTh n).get
  IO.println "thunk"
  IO.println s!"prop task {← IO.hasFinished (mkP n)}"
  let th := mkThP n
  let _ := th.get
  let _ := th.get
  IO.println "prop thunk"
  let t := spawnT n
  IO.println s!"spawned {(mapT t).get}"
  IO.println s!"pures {(pures n).length}"
  IO.println s!"mapped {(mapT (mapE (Task.spawn fun _ => n + 1))).get}"
  IO.println s!"addr {addrTy' (if n > 2 then Nat else String)}"
