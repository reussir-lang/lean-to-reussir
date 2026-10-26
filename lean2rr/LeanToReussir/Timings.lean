/-!
# Stage timings (`L2R_TIMINGS`)

With the environment variable `L2R_TIMINGS` set, lean2rr prints one line
per step of its pipeline on stderr: the wall time since the previous line,
the time since the first one, and the resident memory now and at most
(`VmRSS`, `VmHWM` of /proc/self/status). For profiling the translation;
the generated text does not change.
-/

namespace LeanToReussir

/-- The time of the previous line (`IO.monoMsNow`), and of the first one;
0 before the first. -/
initialize timingLast : IO.Ref (Nat × Nat) ← IO.mkRef (0, 0)

/-- `VmRSS` and `VmHWM` of /proc/self/status, in MB ("?" when unknown). -/
def residentMB : IO (String × String) := do
  let text ← try IO.FS.readFile "/proc/self/status" catch _ => pure ""
  let field (key : String) : String :=
    match (text.splitOn "\n").find? (·.startsWith key) with
    | some line =>
      let kb := (line.drop key.length).trimAscii.takeWhile Char.isDigit
      match kb.toString.toNat? with
      | some n => toString (n / 1024)
      | none => "?"
    | none => "?"
  return (field "VmRSS:", field "VmHWM:")

/-- With `L2R_TIMINGS` set, a line on stderr for the step `what` that just
ended (`detail`: what it made, e.g. a count, which also makes sure the
step's value is computed before the line). -/
def timingMark (what : String) (detail : String := "") : IO Unit := do
  unless (← IO.getEnv "L2R_TIMINGS").isSome do return
  let now ← IO.monoMsNow
  let (last, first) ← timingLast.get
  let (last, first) := if first == 0 then (now, now) else (last, first)
  timingLast.set (now, first)
  let (rss, hwm) ← residentMB
  let secs (ms : Nat) : String :=
    let s := toString (ms / 1000)
    let r := toString (ms % 1000)
    s!"{s}.{"".pushn '0' (3 - r.length)}{r}"
  IO.eprintln s!"lean2rr: timing: {what}: {secs (now - last)} s (at {secs (now - first)} s), RSS {rss} MB, peak {hwm} MB{if detail.isEmpty then "" else s!"; {detail}"}"

end LeanToReussir
