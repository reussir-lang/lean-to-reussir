import Std.Data.HashMap
/-! Runtime test: the `sync` dependents of a promise released inside a free
(the promise held by a container that is freed) run before the next
statement, as natively, where they run on the dropping thread during the
free: promises in an array, an `Option` and a `HashMap` held by an `IO.Ref`
that is set to an empty value. A dependent that reads the reference sees
its new value (the old one is released after the store, as natively), and
dependents that print inside `IO.FS.withIsolatedStreams` are captured.
Promises freed by Reussir's record glue: `RtPromiseFreeGlue`. -/

def watch (flag : IO.Ref Nat) (p : IO.Promise Unit) : BaseIO Unit := do
  let _ ← BaseIO.mapTask (sync := true) (t := p.result?) fun r =>
    if r.isNone then flag.modify (· + 1) else pure ()

def main : IO Unit := do
  let flag ← IO.mkRef 0
  -- an array in a ref
  let reg ← IO.mkRef (#[] : Array (IO.Promise Unit))
  for _ in [0:3] do
    let p ← IO.Promise.new
    reg.modify (·.push p)
    watch flag p
  reg.set #[]
  let f ← flag.get
  IO.println s!"array: {f}"
  -- an Option in a ref
  let r1 ← IO.mkRef (none : Option (IO.Promise Unit))
  let p1 ← IO.Promise.new
  watch flag p1
  r1.set (some p1)
  r1.set none
  IO.println s!"option: {← flag.get}"
  -- a HashMap in a ref
  let r2 ← IO.mkRef (∅ : Std.HashMap Nat (IO.Promise Unit))
  for i in [0:2] do
    let p ← IO.Promise.new
    watch flag p
    r2.modify (·.insert i p)
  r2.set ∅
  IO.println s!"hashmap: {← flag.get}"
  -- dependents that read the reference being set
  let r3 ← IO.mkRef (#[] : Array (IO.Promise Unit))
  let seen ← IO.mkRef (#[] : Array Nat)
  for _ in [0:2] do
    let p ← IO.Promise.new
    r3.modify (·.push p)
    let _ ← BaseIO.mapTask (sync := true) (t := p.result?) fun _ => do
      let n := (← r3.get).size
      seen.modify (·.push n)
  let q ← IO.Promise.new
  r3.set #[q, q, q]
  IO.println s!"sizes the dependents saw: {← seen.get}"
  -- dependents that print, inside withIsolatedStreams
  let r4 ← IO.mkRef (#[] : Array (IO.Promise Unit))
  for i in [0:2] do
    let p ← IO.Promise.new
    r4.modify (·.push p)
    let _ ← BaseIO.mapTask (sync := true) (t := p.result?) fun r =>
      if r.isNone then IO.println s!"request {i} cancelled" |>.catchExceptions (fun _ => pure ()) else pure ()
  let (out, _) ← IO.FS.withIsolatedStreams (do r4.set #[] : IO Unit)
  IO.println s!"captured: {out.quote}"
