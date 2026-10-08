/-! `IO.Process.forceExit` after `main` computed for a while (no scheduling
point), with a task queued before: natively a pool worker runs the task
meanwhile, so its line is out before `_Exit`; lean2rr's `forceExit` has the
effect point of `IO.Process.exit` (hunt HIO3-01). -/

def spin : Nat → UInt64 → UInt64
  | 0, acc => acc
  | n+1, acc => spin n (acc * 6364136223846793005 + 1442695040888963407)

def main (args : List String) : IO Unit := do
  let _ ← IO.asTask (IO.eprintln "task ran")
  -- read after `asTask` (no scheduling point), so the computation stays after it
  let n := ((← IO.getEnv "HIO_SPIN").bind String.toNat?).getD 300000000
  let r := spin n 0
  if r == 42 then IO.eprintln "unlikely"
  match args.headD "force" with
  | "force" => IO.Process.forceExit 0
  | _ => IO.Process.exit 0
