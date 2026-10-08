/-! Runtime test (hunt HTG-02, with one native worker thread, `NAME.pipe`):
`IO.cancel t` as `t`'s last use. Natively `lean_io_cancel` borrows the task
and the caller's decrement follows: first the cancel, then the release.
lean2rr's `l2r_task_cancel` does the same with the task's cell. Before, the
generated code passed the cell's address (`l2r_lcell_addr`, which released
the cell first), and for a finished task the cancel read the index slot of
a freed cell (a read of freed memory that no output shows). Here: a
finished task; a pure task still queued behind a blocker on the one worker,
which the release after the cancel deletes, so it never runs; a running
dedicated task, which sees the cancel. -/
def work (n : Nat) : Nat := dbgTrace "dropped spawn runs" fun _ => n + 1

def main (args : List String) : IO Unit := do
  let n := args.length
  let t1 ← BaseIO.asTask (pure (n + 1))
  let v ← IO.wait t1
  IO.println s!"t1 = {v}"
  -- the last use of `t1`, which has finished
  IO.cancel t1
  let blocker ← IO.asTask (do IO.sleep 300; IO.println "blocker done"; return 1)
  IO.sleep 20
  -- its only reference
  IO.cancel (Task.spawn fun _ => work n)
  let t3 ← IO.asTask (prio := .dedicated) do
    IO.sleep 100
    IO.println s!"t3 canceled: {← IO.checkCanceled}"
  IO.sleep 20
  -- the last use of `t3`, which sleeps
  IO.cancel t3
  let _ ← IO.wait blocker
  IO.println "end"
