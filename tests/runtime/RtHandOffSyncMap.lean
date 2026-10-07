/-! Runtime test (lean2rr's review HR-02): `IO.mapTask (sync := true) f t`
on a finished `t` applies `f` at once on the calling thread
(`lean_task_map_core`): no task, so no "`Task.get` called from a `(sync :=
true)` task" panic when `f` waits. `main` drops a pipe handle whose last
byte the pipe cannot take yet: natively its `fclose` blocks until the child
reads, about a second; `t` finishes at 300 ms; then `main` maps over `t`
with `sync := true`, and `f` waits for `slow` (1.5 s). Natively: "dep 5 7",
then "main after mapTask", and nothing on stderr.

lean2rr's drop hands the byte to a writer thread of lean-runtime and waits
for it at the end of the free (lean-runtime's drain-end hook
`sched::after_drain`), while `t` finishes, so the generated test of `t`
sees it finished, as natively. Before, the test saw `t` unfinished, and
lean-runtime's `depend`, whose wait for the writer let `t` finish, queued
the `sync` dependent: the panic, and the two lines in the other order.
Since lean-runtime's fixes-14, `depend` also runs a `sync` dependent of a
source that finished during that wait at once, inside the call, as the
caller's code (Lean's fast path, as if the test had seen `t` finished). lean-runtime's case `process/handoff_then_sync_map`. Needs `sh`,
`sleep`, `cat` and the default pipe capacity (64 KiB). -/

def main : IO Unit := do
  let t ← BaseIO.asTask (do IO.sleep 300; pure (5 : Nat))
  let slow ← BaseIO.asTask (do IO.sleep 1500; pure (7 : Nat))
  let child ← IO.Process.spawn
    { cmd := "sh", args := #["-c", "sleep 1; cat > /dev/null"], stdin := .piped }
  let (stdin, child) ← child.takeStdin
  stdin.write (ByteArray.mk (Array.replicate 65536 120))
  stdin.flush
  stdin.putStr "x"
  -- `stdin`'s last use: it is closed here, before the map
  let d ← IO.mapTask (sync := true) (fun v => do
      let w ← IO.wait slow
      IO.println s!"dep {v} {w}") t
  IO.println "main after mapTask"
  let _ ← IO.wait d
  let _ ← child.wait
  pure ()
