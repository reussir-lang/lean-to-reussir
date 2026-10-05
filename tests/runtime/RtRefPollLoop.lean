/-! Runtime test: a loop that only reads a reference, until a task sets it, ends.
Natively the task runs on a worker thread while `main` spins. lean2rr runs both
on one thread: in a program that creates tasks every 1000th reference read is a
polling point (lean-runtime's `ref_read`, glue item 5; `leanrt::refs`), where the
deferred task starts; without it `main` would spin forever. The task sets the
flag 200 times, 1 ms apart: natively a concurrent `get` can put the old value
back over one `set` (LB-01), never over all of them. -/

def main : IO Unit := do
  let flag ← IO.mkRef false
  let _t ← IO.asTask do
    for _ in [0:200] do
      flag.set true
      IO.sleep 1
  while !(← flag.get) do
    pure ()
  IO.println "flag seen"
