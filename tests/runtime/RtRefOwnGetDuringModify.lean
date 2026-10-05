/-! Runtime test (review RS4-01; lean-runtime's case
`refs/own_get_during_modify`): the taker's own `get` during its `modify`
waits. `r.modify f` takes the pair out of `r`, so `r` is empty while `f`
runs. `f` replaces the pair, so the old pair, and with it `some p`, the last
reference to the unresolved promise `p`, is freed between the take and the
store. Dropping it resolves `p` with `none`, and `p`'s `sync` dependent runs
then, on the thread of the `modify`, while `r` is taken. The dependent
signals `main` (`reached`), then reads `r`. Natively `r` is multi-threaded
(tasks' closures captured it): the read spins until `modify`'s store, which
never comes, so that thread hangs, and `main` prints and ends the process
(`IO.Process.exit 0`). lean2rr's dependent read the placeholder before (a
value never stored); now it waits, as natively (lean-runtime's
`ref_keyed`). No sleep: the signal reaches `main` before the wait, and the
exit ends the waiting task. -/

def main : IO Unit := do
  let n := 41
  let p ← IO.Promise.new (α := Nat)
  let reached ← IO.Promise.new (α := Unit)
  let r ← IO.mkRef (n, some p)
  let _d ← IO.mapTask (t := p.result?) (sync := true) fun v => do
    reached.resolve ()
    let (k, _) ← r.get
    IO.eprintln s!"dependent: promise {v}, reference holds {k}"
  let _t ← IO.asTask (prio := .dedicated) do
    IO.eprintln "modify"
    r.modify fun (k, _) => (k + 1, none)
    IO.eprintln s!"after modify: {(← r.get).1}"
  let _ ← IO.wait reached.result?
  IO.eprintln "main: the dependent waits for the reference"
  IO.Process.exit 0
