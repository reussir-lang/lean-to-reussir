/-! Runtime test: a `null` stream when `/dev/null` cannot be opened (LB-17
in lean-runtime's docs/lean-bugs.md; plan §10, "Runtime: Lean bugs we do
not reproduce"). `RtProcessNullOpenFails.pipe` runs the program under
`ulimit -n 64` with `line1` and `line2` on standard input. It opens handles
until `EMFILE`, keeps them open to the end, and spawns. Natively the forked
child's `open("/dev/null")` fails unchecked, `dup2(-1, n)` fails, and the
program runs on the parent's own descriptor n: the child of
`stdout := .null` writes on the parent's standard output, and the child of
`stdin := .null` reads the parent's first line, so the parent reads
`line2`. lean2rr opens `/dev/null` in the parent before the spawn, so the
spawn fails with `EMFILE`, as a failed pipe does, and the parent reads
`line1`. Then the program frees descriptors and spawns again, printing
how many are free before and after each spawn (counted by opening handles
until `EMFILE`, then closing them):
- two free, `stdin := .null` and a piped stdout: the pipe takes both, then
  `/dev/null` cannot be opened (natively in the child, which runs on the
  parent's stdin); lean2rr's failed spawn closes the pipe it made, so two
  are free again;
- three free, the same spawn: it succeeds in both, with an empty stdin,
  and three are free again afterwards (the parent closed its `/dev/null`);
- two free, a piped stdout and `stderr := .null`: natively the child has
  closed the pipe's read end before it opens `/dev/null`, so the spawn
  succeeds; lean2rr opens `/dev/null` in the parent next to both pipe ends
  and fails with `EMFILE`. A spawn in which some `null` stream follows a
  piped one needs exactly one more free descriptor than natively (one in
  all, however many such streams; plan §10, LB-17).
-/

partial def exhaust (acc : Array IO.FS.Handle) : IO (Array IO.FS.Handle) := do
  match ← (IO.FS.Handle.mk "/dev/null" .read).toBaseIO with
  | .ok h => exhaust (acc.push h)
  | .error _ => pure acc

/-- How many descriptors are free (the handles opened to count them are closed on return). -/
def countFree : IO Nat := do
  return (← exhaust #[]).size

/-- Closes the last `n` handles, here and now (a pure `pop` may be moved by the compiler). -/
@[noinline] def release (hs : Array IO.FS.Handle) : Nat → IO (Array IO.FS.Handle)
  | 0 => pure hs
  | n + 1 => release hs.pop n

def readLine : String :=
  "if read x; then echo \"  child: read $x\"; else echo '  child: no input'; fi"

def main : IO Unit := do
  let hs ← exhaust #[]
  IO.println "stdout null:"
  (← IO.getStdout).flush
  try
    let c ← IO.Process.spawn
      { cmd := "sh", args := #["-c", "echo '  child: written to the parent'"], stdout := .null }
    IO.println s!"  exit {← c.wait}"
  catch e => IO.println s!"  spawn failed: {e}"
  IO.println "stdin null:"
  (← IO.getStdout).flush
  try
    let c ← IO.Process.spawn { cmd := "sh", args := #["-c", readLine], stdin := .null }
    IO.println s!"  exit {← c.wait}"
  catch e => IO.println s!"  spawn failed: {e}"
  IO.println s!"parent reads: {(← (← IO.getStdin).getLine).trimAscii}"
  let hs ← release hs 2
  IO.println s!"stdin null, stdout piped, {← countFree} descriptors free:"
  try
    let c ← IO.Process.spawn { cmd := "true", stdin := .null, stdout := .piped }
    IO.println s!"  exit {← c.wait}"
  catch e => IO.println s!"  spawn failed: {e}"
  IO.println s!"  descriptors free afterwards: {← countFree}"
  let hs ← release hs 1
  IO.println s!"stdin null, stdout piped, {← countFree} descriptors free:"
  try
    let c ← IO.Process.spawn { cmd := "sh", args := #["-c", readLine], stdin := .null, stdout := .piped }
    IO.print (← c.stdout.readToEnd)
    IO.println s!"  exit {← c.wait}"
  catch e => IO.println s!"  spawn failed: {e}"
  IO.println s!"  descriptors free afterwards: {← countFree}"
  let hs := hs.push (← IO.FS.Handle.mk "/dev/null" .read)
  IO.println s!"stdout piped, stderr null, {← countFree} descriptors free:"
  (← IO.getStdout).flush
  try
    let c ← IO.Process.spawn
      { cmd := "sh", args := #["-c", "echo '  child: stderr, discarded' >&2; echo '  child: stdout'"],
        stdout := .piped, stderr := .null }
    IO.print (← c.stdout.readToEnd)
    IO.println s!"  exit {← c.wait}"
  catch e => IO.println s!"  spawn failed: {e}"
  IO.println s!"  descriptors free afterwards: {← countFree}"
  -- keeps the handles open until here
  IO.println s!"handles kept open: {decide (hs.size > 0)}"
