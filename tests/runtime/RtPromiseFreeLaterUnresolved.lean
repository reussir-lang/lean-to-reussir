/-! Runtime test (the store-with-resolve shape of lean-runtime's deferred
resolutions, its review RW1-05): a free of `#[pB, pA]` reaches `pA` first
(an array from its last element). Natively `pA`'s `sync` dependent runs
there, before the free reaches `pB`, so `pB` is still unresolved, both for
the dependent itself (part 1) and for another context that looks while the
dependent blocks (part 2). lean2rr resolves both after the free, in that
order, each with its cell's store (`leanrt::task::defer_promise_drop`), so
`pB` looks unresolved too; with the store made inside the free (lean2rr's
shape before switch step 6), part 2's observer saw `pB` finished. -/

def part1 : IO Unit := do
  let pA ← IO.Promise.new (α := Unit)
  let pB ← IO.Promise.new (α := Unit)
  let resB := pB.result?
  let _ ← IO.mapTask (sync := true) (t := pA.result?) fun _ => do
    IO.println s!"A: pB finished {← IO.hasFinished resB}"
  let _ ← IO.mapTask (sync := true) (t := resB) fun _ => IO.println "B: dependent"
  let holder ← IO.mkRef #[pB, pA]
  holder.set #[]
  IO.println "part 1: after the free"

def part2 : IO Unit := do
  let gate ← IO.Promise.new (α := Unit)
  let aStarted ← IO.Promise.new (α := Unit)
  let pA ← IO.Promise.new (α := Unit)
  let pB ← IO.Promise.new (α := Unit)
  let resB := pB.result?
  let _ ← IO.mapTask (sync := true) (t := pA.result?) fun _ => do
    IO.println "A: dependent starts"
    aStarted.resolve ()
    let _ ← IO.wait gate.result?
    IO.println "A: dependent ends"
  let _ ← IO.mapTask (sync := true) (t := resB) fun r => IO.println s!"B: dependent ({r.isSome})"
  let obs ← IO.asTask (prio := .dedicated) do
    let _ ← IO.wait aStarted.result?
    IO.println s!"observer: pB finished {← IO.hasFinished resB}"
    gate.resolve ()
  let holder ← IO.mkRef #[pB, pA]
  holder.set #[]
  IO.println "part 2: after the free"
  let _ ← IO.wait obs

def main : IO Unit := do
  part1
  part2
