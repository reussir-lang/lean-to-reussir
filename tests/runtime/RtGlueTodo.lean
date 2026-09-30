/-! Runtime test: IO externs whose results are `EST.Out`/`ST.Out` (lean2rr
wraps payload primitives `l2r_io_*`), `dbgTrace` at a type stored boxed, and
`Substring` (externs implemented by exported Lean code). -/

def main (args : List String) : IO Unit := do
  let k := args.length
  let t := dbgTrace "trace at Nat" fun _ => k + 41
  IO.println s!"dbgTrace {t}"
  let task ← BaseIO.asTask (pure (k + 7))
  IO.println s!"asTask {task.get}"
  let t0 ← IO.monoMsNow
  let t1 ← IO.monoMsNow
  let n0 ← IO.monoNanosNow
  IO.println s!"clock monotone {decide (t0 ≤ t1)} {decide (n0 > 0)}"
  let bytes ← IO.getRandomBytes 16
  IO.println s!"random bytes {bytes.size}"
  let ss := "  hello world  ".toSubstring
  IO.println s!"substring {ss.trim} {ss.drop 2 |>.takeWhile Char.isAlpha} {(ss.dropWhile (· == ' ')).toString.length} {ss.front} {ss.isEmpty}"
