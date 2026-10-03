import Std.Internal.UV
open Std.Internal.UV
/-! Runtime test: `Timer.stop` drops the promise of `next` unresolved. Its
`sync` dependents run where it is dropped: natively in `stop`, on the
calling thread. Here `result!` of that promise (`Option.getOrBlock!`)
panics and blocks `main` forever at the stop; a task goes on and exits
the program. -/
def main : IO Unit := do
  let tm ← Timer.mk 100000 false
  let p ← tm.next
  let t := p.result!
  let _ ← IO.asTask (prio := .dedicated) (do let v ← IO.wait t; IO.eprintln s!"got {v}")
  let _ ← IO.asTask (prio := .dedicated) (do
    IO.sleep 300
    IO.eprintln "a task exits"
    IO.Process.exit 0 : IO Unit)
  IO.sleep 50
  IO.eprintln "main stops the timer"
  tm.stop
  IO.eprintln "main after stop"
