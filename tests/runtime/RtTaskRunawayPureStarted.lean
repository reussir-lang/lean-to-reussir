/-! Runtime test (from lean-runtime's case tasks/runaway_pure_task_started,
an exit probe): a pure task that a worker has surely started (main
holds it across a 50 ms sleep) and that main then drops still runs to
completion before the process exits, so a runaway one keeps the process
alive. Natively main prints `main done false false` and the process then
runs until the `.pipe`'s timeout (exit 124). lean2rr starts the task during
main's sleep and never gets control back, so main prints nothing. -/

partial def spin (x acc : UInt64) : UInt64 :=
  if x == 0 then acc else spin (x * 6364136223846793005 + 1442695040888963407) (acc + 1)

def main (args : List String) : IO Unit := do
  let s := args.head!.toNat!.toUInt64 ||| 1
  let ms := args[1]!.toNat!
  let t := Task.spawn fun _ => spin s 0
  let f1 ← IO.hasFinished t
  IO.sleep ms.toUInt32
  let f2 ← IO.hasFinished t
  IO.eprintln s!"main done {f1} {f2}"
