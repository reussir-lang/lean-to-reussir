/-! Runtime test (lean-runtime's case `tasks/wait_dep_mid_walk`, review RS1S-16 of
its scheduler): a task waited for (`IO.wait`, `IO.waitAny`, polled) while the
walk of its source's dependents has not queued it yet (a newer `sync`
dependent sleeps in the walk): the wait lasts until the walk queues it, as
natively. lean2rr's own scheduler deviated here; lean-runtime's, which lean2rr
uses since switch step 4, does not. The case's note: `main` waits for an async
dependent of `b` while the walk of `b`'s dependents is held up in a newer
`sync` dependent, which sleeps on the worker that finished `b`. Natively the
walk queues the async dependent only once the `sync` one returns, and `main`
waits until then. -/

def main (args : List String) : IO Unit := do
  let ms := args.map String.toNat!
  let b ← IO.asTask (IO.sleep ms[0]!.toUInt32)
  let a ← IO.mapTask (fun _ => IO.eprintln "async dep ran") b
  let _ ← IO.mapTask (sync := true) (fun _ => do
    IO.sleep ms[2]!.toUInt32
    IO.eprintln "sync dep done") b
  IO.sleep ms[1]!.toUInt32
  let _ ← IO.wait a
  IO.eprintln "main got a"
