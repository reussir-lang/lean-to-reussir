/-! Runtime test (lean-runtime's W3 is unreachable from Lean code; its
rule R3): the `sync` dependent of a promise released inside a container's
free reaches a wait that blocks, and waits outside the free. Task `T`
signals `main` (`taking`), then holds `r` in a `modify` whose function waits
for promise `go`. `main` then frees the array that holds promise `p`: its
dependent resolves `go`, then reads `r`, which `T` holds, so it waits for
`T`'s store, then prints. Natively the dependent runs inside the free, on
`main`'s thread, and spins until the store. In lean2rr the free runs no Lean
code: the dependent runs once the free is over (lean-runtime's `defer`,
`run_deferred`), before `main`'s next statement, and its wait blocks there;
inside the free it would be lean-runtime's W3 panic (an abort). -/

def main : IO Unit := do
  let go ← IO.Promise.new (α := Nat)
  let taking ← IO.Promise.new (α := Unit)
  let r ← IO.mkRef 1
  let t ← IO.asTask (prio := .dedicated) do
    taking.resolve ()
    r.modify fun k => k + go.result?.get.getD 0
  let _ ← IO.wait taking.result?
  let p ← IO.Promise.new (α := Unit)
  let _d ← IO.mapTask (t := p.result?) (sync := true) fun _ => do
    go.resolve 41
    let _ ← r.get
    IO.println "dependent: read the reference"
  let holder ← IO.mkRef #[p]
  holder.set #[]
  IO.println "main: after the free"
  let _ ← IO.wait t
  IO.println s!"main: the reference holds {← r.get}"
