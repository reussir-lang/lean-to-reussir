import Std.Internal.UV.Timer
/-! Runtime test: a repeating `Std.Internal.UV.Timer` of period 0 is libuv's
timer with timeout 0 and repeat 0, which fires once: the next tick never
comes, until `reset` starts it again (once more). -/
open Std.Internal.UV

/-- Whether `p` is resolved within about `ms` milliseconds. -/
def within (p : IO.Promise Unit) (ms : Nat) : IO Bool := do
  let deadline := (← IO.monoMsNow) + ms
  while (← IO.monoMsNow) < deadline do
    if ← p.isResolved then return true
    IO.sleep 10
  p.isResolved

def main : IO Unit := do
  let t ← Timer.mk 0 true
  let p1 ← t.next
  IO.println s!"first tick {← within p1 2000}"
  let p2 ← t.next
  IO.println s!"second tick {← within p2 300}"
  t.reset
  IO.println s!"second tick after reset {← within p2 2000}"
  let p3 ← t.next
  IO.println s!"third tick {← within p3 300}"
  t.stop
