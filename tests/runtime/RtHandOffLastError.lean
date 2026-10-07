/-! Runtime test (lean-runtime-side hunt HCO-01, switch step 14): a pipe
handle's last reference goes inside its own primitive, with the pipe full.
Natively the primitive returns its own result, and the handle's `fclose`
then blocks until the child reads (about half a second). lean2rr's drop
hands the last bytes to a writer thread of lean-runtime and waits for it
(the drain-end hook `sched::after_drain`) while the other contexts run,
after the primitive recorded its outcome; a task's IO meanwhile recorded
its own outcome in the same slot, and the program read the task's:
- round 1: `putStr` succeeds, the task's open fails (caught): `putStr`
  failed with the task's "no such file or directory";
- round 2: `truncate` of the pipe fails (`ftell` gives -1, so
  `ftruncate` gives `EINVAL`, with no flush of the buffered byte), the
  task's open succeeds: the failure was lost.
Each context now has its own outcome (leanrt's `fs::LastError`, exchanged
at each switch). Needs `sh`, `sleep`, `cat` and the default pipe capacity
(64 KiB). -/

def child : IO (IO.FS.Handle × IO.Process.Child { stdin := .null, stdout := .inherit, stderr := .inherit }) := do
  let c ← IO.Process.spawn
    { cmd := "sh", args := #["-c", "sleep 0.5; cat > /dev/null"], stdin := .piped }
  let (stdin, c) ← c.takeStdin
  stdin.write (ByteArray.mk (Array.replicate 65536 120))
  stdin.flush
  return (stdin, c)

def round1 : IO Unit := do
  let b ← IO.asTask (do
    IO.sleep 100
    try
      let _ ← IO.FS.Handle.mk "/nonexistent-rt-handoff-dir/x" .read
      pure ()
    catch _ => pure ()
    IO.sleep 1500)
  let (stdin, c) ← child
  -- the handle's last use: its last reference goes inside this call
  try
    stdin.putStr "x"
    IO.println "round 1: putStr ok"
  catch e => IO.println s!"round 1: putStr failed: {e}"
  let _ ← IO.wait b
  IO.println s!"round 1: child {← c.wait}"

def round2 : IO Unit := do
  let b ← IO.asTask (do
    IO.sleep 100
    let _ ← IO.FS.Handle.mk "/dev/null" .read
    IO.sleep 1500)
  let (stdin, c) ← child
  stdin.putStr "x"
  -- the handle's last use fails; its last reference goes inside the call,
  -- which closes it with "x" buffered
  try
    stdin.truncate
    IO.println "round 2: truncate ok"
  catch e => IO.println s!"round 2: truncate failed: {e}"
  let _ ← IO.wait b
  IO.println s!"round 2: child {← c.wait}"

def main : IO Unit := do
  round1
  round2
