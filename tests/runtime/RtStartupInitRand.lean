/-! Runtime test: `IO.rand` reads the generator that the library's
initializer `IO.stdGenRef` seeded at startup, and does not seed it again:
once every descriptor is taken (`RtStartupInitRand.pipe` runs the program
under `ulimit -n 64`), `/dev/urandom` cannot be opened, and `IO.rand` still
works. After `IO.setRandSeed`, the numbers are those of Lean's generator
(`stdNext`), the same in both builds. -/

partial def fill (acc : Array IO.FS.Handle) : IO (Array IO.FS.Handle) := do
  match ← (IO.FS.Handle.mk "/dev/null" .read).toBaseIO with
  | .ok h => if acc.size < 1000 then fill (acc.push h) else return acc
  | .error _ => return acc

def main : IO Unit := do
  let hs ← fill #[]
  match ← (IO.getRandomBytes 8).toBaseIO with
  | .ok _ => IO.println "getRandomBytes 8: ok"
  | .error e => IO.println s!"getRandomBytes 8: {e}"
  let r ← IO.rand 1 6
  IO.println s!"rand 1 6 in range {decide (1 ≤ r ∧ r ≤ 6)}"
  IO.setRandSeed 42
  let mut xs := #[]
  for _ in [0:5] do xs := xs.push (← IO.rand 0 1000000)
  IO.println s!"seed 42: {xs}"
  -- The handles stay open until here.
  IO.println s!"descriptors exhausted {decide (hs.size > 0)}"
