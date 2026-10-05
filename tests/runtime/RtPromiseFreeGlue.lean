/-! Runtime test: as `RtPromiseFreeSync`, with the promises in records
(a structure in an `Option`, the cells of a `List` after the first, a
list of structures) held by an `IO.Ref` that is overwritten: their
`sync` dependents run before the next statement, as natively. The old
value is freed by the runtime (`leanrt::drop::release`), and the
dependents run when that free ends. -/

structure Pending where
  id : Nat
  p : IO.Promise Unit

def watch (flag : IO.Ref Nat) (p : IO.Promise Unit) : BaseIO Unit := do
  let _ ← BaseIO.mapTask (sync := true) (t := p.result?) fun r =>
    if r.isNone then flag.modify (· + 1) else pure ()

def main : IO Unit := do
  let flag ← IO.mkRef 0
  -- a structure in an Option in a ref
  let r1 ← IO.mkRef (none : Option Pending)
  let p1 ← IO.Promise.new
  watch flag p1
  r1.set (some { id := 1, p := p1 })
  r1.set none
  IO.println s!"structure: {← flag.get}"
  -- a list in a ref
  let r2 ← IO.mkRef ([] : List (IO.Promise Unit))
  for _ in [0:3] do
    let p ← IO.Promise.new
    watch flag p
    r2.modify (p :: ·)
  r2.set []
  IO.println s!"list: {← flag.get}"
  -- a list of structures in a ref
  let r3 ← IO.mkRef ([] : List Pending)
  for i in [0:3] do
    let p ← IO.Promise.new
    watch flag p
    r3.modify ({ id := i, p } :: ·)
  r3.set []
  IO.println s!"list of structures: {← flag.get}"
