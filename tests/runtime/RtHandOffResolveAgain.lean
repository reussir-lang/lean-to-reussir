/-! Runtime test (lean2rr's review HR-01): a promise resolved twice keeps
its first value (Init/System/Promise.lean: "Only the first call to this
function has an effect"). `main` drops a pipe handle whose last byte the
pipe cannot take yet: natively its `fclose` blocks until the child reads,
about a second. Task B resolves the promise with 2 at 300 ms; then `main`
resolves it with 1, which has no effect. Natively: "B sees (some 2)", then
"main sees (some 2)".

lean2rr's drop hands the byte to a writer thread of lean-runtime and waits
for it at the end of the free (lean-runtime's drain-end hook
`sched::after_drain`), while the other contexts run, as natively the drop
waited in `fclose`. Before, nothing waited at the drop: the generated
resolution tested the promise, then its store waited for the writer (a
publication), during which B resolved the promise, and stored 1 over 2
("main sees (some 1)"). The test and the store are now made inside
lean-runtime's `resolve`, after its own wait, so no wait can come between
them. lean-runtime's case `process/handoff_then_resolve_again`. Needs `sh`,
`sleep`, `cat` and the default pipe capacity (64 KiB). -/

def main : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  let b ← IO.asTask (do
    IO.sleep 300
    p.resolve 2
    let v ← IO.wait p.result?
    IO.println s!"B sees {v}")
  let child ← IO.Process.spawn
    { cmd := "sh", args := #["-c", "sleep 1; cat > /dev/null"], stdin := .piped }
  let (stdin, child) ← child.takeStdin
  stdin.write (ByteArray.mk (Array.replicate 65536 120))
  stdin.flush
  stdin.putStr "x"
  -- `stdin`'s last use: it is closed here, before the resolution
  p.resolve 1
  let v ← IO.wait p.result?
  IO.println s!"main sees {v}"
  let _ ← IO.wait b
  let _ ← child.wait
  pure ()
