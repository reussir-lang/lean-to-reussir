/-! Runtime test (hunt of flatten-structs and conversions, judged a
documented divergence: plan §10, "Release time of pure tasks"): when a
pure task that a structure holds is released. It runs on one worker
(`.pipe`: `LEAN_NUM_THREADS=1`), queued behind a blocker; a queued pure
task whose last reference goes is deleted and never runs, otherwise it
runs once the blocker ends.
- `report`: `j` is only read before the wait. Natively `j` is borrowed,
  so the caller keeps it, and its task, until `report` returns, and the
  task runs; Reussir releases `j` at its last use, before the wait.
- `loopJ`: a loop over a structure holding a task; at the exit `j.n` is
  read after the wait. flatten-structs splits `j`, and the task field,
  which no code reads, is released at the start of the exit's path.
- `viaJp`: a structure built in two branches, a join point's parameter
  that flatten-structs splits; its task field is released at the start of
  the join point's body.
Natively each task prints its `dbgTrace` line on stderr; through lean2rr
none does (the expectation files RtTaskDropReleaseTime.native.err and
.l2r.err, so that a change on either side shows). stdout is the same. -/
set_option linter.unusedVariables false

structure Job where
  t : Task Nat
  n : Nat

-- `j` is only read and compared (`Nat.beq` borrows): borrowed natively, so
-- the caller keeps `j`, and its task, until `report` returns
@[noinline] def report (j : Job) (blocker : Task (Except IO.Error Nat)) : IO Nat := do
  if j.n == 3 then IO.println "report: n is 3" else IO.println "report: n is not 3"
  let v ← IO.wait blocker
  IO.sleep 50
  match v with
  | .ok v => return v
  | .error _ => return 0

-- a loop over a structure holding a task (`j.t` goes into a constructor:
-- owned natively); at the exit `j` is read after the wait
@[noinline] def loopJ (j : Job) (blocker : Task (Except IO.Error Nat)) : Nat → IO Nat
  | 0 => do
    let v ← IO.wait blocker
    IO.sleep 50
    match v with
    | .ok v => return j.n + v
    | .error _ => return j.n
  | k + 1 => do
    IO.println s!"step {k}"
    loopJ { j with n := j.n + 1 } blocker k

-- a structure built in two branches (a join point's parameter), read
-- after the wait
@[noinline] def viaJp (t : Task Nat) (c : Bool) (blocker : Task (Except IO.Error Nat)) : IO Nat := do
  let j : Job := if c then { t, n := 10 } else { t, n := 20 }
  let v ← IO.wait blocker
  IO.sleep 50
  match v with
  | .ok v => return j.n + v
  | .error _ => return j.n

def main (args : List String) : IO Unit := do
  let n := args.length
  let blocker ← IO.asTask (do IO.sleep 200; return 1)
  IO.sleep 20
  let t := Task.spawn fun _ => dbgTrace "report's task runs" fun _ => n + 42
  let v ← report { t, n := n + 3 } blocker
  IO.println s!"v = {v}"
  let blocker2 ← IO.asTask (do IO.sleep 200; return 2)
  IO.sleep 20
  let t2 := Task.spawn fun _ => dbgTrace "loopJ's task runs" fun _ => n + 43
  let r ← loopJ { t := t2, n := n } blocker2 3
  IO.println s!"r = {r}"
  let blocker3 ← IO.asTask (do IO.sleep 200; return 3)
  IO.sleep 20
  let t3 := Task.spawn fun _ => dbgTrace "viaJp's task runs" fun _ => n + 44
  let w ← viaJp t3 (n == 0) blocker3
  IO.println s!"w = {w}"
  IO.sleep 50
  IO.println "end"
