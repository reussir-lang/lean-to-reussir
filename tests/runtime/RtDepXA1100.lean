/-! Runtime test: case `A1100` of the shared dependent-type corpus (programs
built by another translator's team and checked against native Lean). It
checks: Chapter 06 A4 io fixture A1100 (D34 (b), (g) -/
def main (args : List String) : IO Unit := do
  let n := ((args[0]?).bind String.toNat?).getD 1
  let sleepMs := ((args[1]?).bind String.toNat?).getD 200
  let p ← IO.Promise.new (α := Nat)
  let reached ← IO.Promise.new (α := Unit)
  let r ← IO.mkRef (n, some p)
  let _d ← IO.mapTask (t := p.result?) (sync := true) fun v => do
    reached.resolve ()
    let (k, _) ← r.get
    IO.println s!"dependent: promise {v}, reference holds {k}"
  let _t ← IO.asTask (prio := .dedicated) do
    IO.println "modify"
    r.modify fun (k, _) => (k + 1, none)
    IO.println s!"after modify: {(← r.get).1}"
  let _ ← IO.wait reached.result?
  IO.sleep sleepMs.toUInt32
  IO.println "main: the dependent waits for the reference"
  IO.Process.exit 0
