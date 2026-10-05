/-! Runtime test (review RS4-04): no context suspends inside a free.
`main` drops an array holding (promise `p`, handle `stdin`) in one free. The
free reaches the handle first (a record's last field first): its close runs
in lean-runtime's no-suspend scope, and its flush, the pipe being full (the
child reads only after a second), hands the last byte to a writer thread.
The free then reaches the unresolved promise and resolves it with `none`:
its cell store is a publication, which waited for `main`'s writer, so
`main` suspended with the thread's free still running, and task B's drop of
its own promise `q` went onto that free. Natively (and with the store in the
no-suspend scope, `leanrt::task::drop_promise_now`) B's drop resolves `q`
and runs its `sync` dependent at once: "B: q's dependent" comes before "B:
after dropping q". Needs `sh`, `sleep`, `cat` and the default pipe capacity
(64 KiB). -/

def main : IO Unit := do
  let child ← IO.Process.spawn
    { cmd := "sh", args := #["-c", "sleep 1; cat > /dev/null"], stdin := .piped }
  let (stdin, child) ← child.takeStdin
  -- Fill the pipe exactly (64 KiB), then leave one byte in the handle's buffer.
  stdin.write (ByteArray.mk (Array.replicate 65536 120))
  stdin.flush
  stdin.putStr "x"
  -- Task B: starts, sleeps, then drops its own promise `q`.
  let b ← IO.asTask do
    IO.sleep 200
    let q ← IO.Promise.new (α := Unit)
    let _ ← IO.mapTask (t := q.result?) (sync := true) fun _ => IO.eprintln "B: q's dependent"
    IO.eprintln "B: after dropping q"
  IO.sleep 50
  let p ← IO.Promise.new (α := Unit)
  let arr : Array (IO.Promise Unit × IO.FS.Handle) := #[(p, stdin)]
  -- `arr`'s last use: it is freed right after, in one free.
  IO.eprintln s!"main: dropping {arr.size} pair"
  let _ ← IO.wait b
  let c ← child.wait
  IO.eprintln s!"main: child exited {c}"
