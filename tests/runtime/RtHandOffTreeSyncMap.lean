/-! Runtime test (lean2rr's review HR-02, the drain's form):
`RtHandOffSyncMap` with the pipe handle inside a tree. The handle is closed
when the tree is freed, after `Tree.count`'s last use of it: in lean2rr
inside the drain of Reussir's free of the tree, which reaches the handle
in an array (its close is put off to that point of the drain). Natively
the same as `RtHandOffSyncMap`: "dep 5 7", then "main after mapTask", and
nothing on stderr. The drain's end (Reussir's drain-end hook, leanrt's
`task::drained`) waits for the writer thread the close handed the last
byte to (lean-runtime's `sched::after_drain`), before the map tests `t`.
lean-runtime's case `process/handoff_in_tree_then_sync_map`. Needs `sh`,
`sleep`, `cat` and the default pipe capacity (64 KiB). -/

inductive Tree where
  | node (h : Option IO.FS.Handle) (kids : Array Tree)

@[noinline] def Tree.count : Tree → Nat
  | .node _ ks => ks.size

def main : IO Unit := do
  let t ← BaseIO.asTask (do IO.sleep 300; pure (5 : Nat))
  let slow ← BaseIO.asTask (do IO.sleep 1500; pure (7 : Nat))
  let child ← IO.Process.spawn
    { cmd := "sh", args := #["-c", "sleep 1; cat > /dev/null"], stdin := .piped }
  let (stdin, child) ← child.takeStdin
  stdin.write (ByteArray.mk (Array.replicate 65536 120))
  stdin.flush
  stdin.putStr "x"
  let tr := Tree.node none #[Tree.node (some stdin) #[]]
  if tr.count == 7 then IO.println "never"
  let d ← IO.mapTask (sync := true) (fun v => do
      let w ← IO.wait slow
      IO.println s!"dep {v} {w}") t
  IO.println "main after mapTask"
  let _ ← IO.wait d
  let _ ← child.wait
  pure ()
