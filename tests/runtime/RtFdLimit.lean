/-! Runtime test: the descriptors open at startup, and how many files a
program can open before `EMFILE`. Natively libuv's 8 descriptors are open
before `main` (numbers 3 to 10); lean2rr's runtime opens the same ones.
`RtFdLimit.pipe` runs the program under `ulimit -n 64` (and once with stdin
closed). The loop stops at 1000 handles in any case. -/
def openUntilFull : Nat → Array IO.FS.Handle → IO (Array IO.FS.Handle × String)
  | 0, acc => return (acc, "limit not reached")
  | n + 1, acc => do
    match ← (IO.FS.Handle.mk "/dev/null" .read).toBaseIO with
    | .ok h => openUntilFull n (acc.push h)
    | .error e => return (acc, toString e)

def main : IO Unit := do
  let entries ← System.FilePath.readDir "/proc/self/fd"
  let mut fds : Array Nat := #[]
  for e in entries do
    if let some n := e.fileName.toNat? then fds := fds.push n
  -- The listing's own directory descriptor is the first free number.
  IO.println s!"open at startup: {fds.qsort (· < ·)}"
  let (hs, err) ← openUntilFull 1000 #[]
  IO.println s!"opened {hs.size} more, then: {err}"
