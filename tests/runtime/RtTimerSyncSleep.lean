import Std.Internal.UV
open Std.Internal.UV
/-! Runtime test: a `sync` dependent of a timer's promise sleeps (natively
on libuv's thread, which blocks); another timer fires meanwhile, and
`main` waits for it. Nothing runs while the dependent sleeps: the process
uses next to no processor time (no busy wait). -/

-- The processor time used so far (user + system), in clock ticks.
def cpuTicks : IO Nat := do
  let s ← IO.FS.readFile "/proc/self/stat"
  let rest := (s.splitOn ") ").getLast!
  let fs := rest.splitOn " "
  return fs[11]!.toNat! + fs[12]!.toNat!

def main : IO Unit := do
  let t1 ← Timer.mk 10 false
  let p1 ← t1.next
  let _d ← BaseIO.mapTask (sync := true) (t := p1.result?) fun _ => do
    IO.sleep 1500
    return ()
  let t2 ← Timer.mk 100 false
  let p2 ← t2.next
  let r ← IO.wait p2.result?
  IO.println s!"t2 fired {r.isSome}"
  let c ← cpuTicks
  IO.println s!"processor time below 0.5 s: {decide (c < 50)}"
