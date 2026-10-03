/-! Runtime test: as `RtPromiseFreeSync`, with the promises freed by
Reussir's record glue (a structure in an `Option` held by an `IO.Ref`, the
cells of a `List` after the first, a list of structures): their `sync`
dependents run before the next statement, as natively. lean2rr's runtime
sees the end of such a free only through Reussir's
`__reussir_drop_drained` (local Reussir patch 0040): without it the
dependents run at the next output, block or question about a task
(`RtPromiseFreeGlue.xfail`). -/

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
