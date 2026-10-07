/-! Runtime test: case `A830` of the shared dependent-type corpus (programs
built by another translator's team and checked against native Lean). It
checks: `IO.mapTask (sync := true)` whose action starts a task with
`IO.asTask` and discards it. -/
@[noinline] def gen {α : Type} [Inhabited α] (x : α) (b : Task (Except IO.Error Nat)) : IO α := do
  let _ ← IO.bindTask b (fun _ => IO.asTask (pure ()))
  let t ← IO.asTask (pure x)
  match ← IO.wait t with
  | .ok v => return v
  | .error _ => return default

def main (args : List String) : IO Unit := do
  let k := args.length
  let b ← IO.asTask (pure (k + 1))
  let _ ← IO.mapTask (sync := true) (fun _ => do
    let _ ← IO.asTask (pure (k * 2))) b
  let t ← IO.mapTask (sync := true) (fun _ => do
    let _ ← IO.asTask (pure ())) b
  match ← IO.wait t with
  | .ok _ => IO.println "t ok"
  | .error e => IO.println s!"t err {e}"
  let _ ← IO.mapTask (fun r => do
    let _ ← IO.asTask (pure r)) b
  let u ← IO.bindTask b (fun r => IO.asTask (pure (r.toOption.getD 0 + 10)))
  match ← IO.wait u with
  | .ok v => IO.println s!"u {v}"
  | .error e => IO.println s!"u err {e}"
  let w ← IO.asTask (do let _ ← IO.asTask (pure k); pure ())
  let _ ← IO.wait w
  let p := Task.spawn (fun _ => if k > 100 then some k else none)
  IO.println s!"p {p.get} b {(← IO.wait b).toOption}"
  if k > 100 then
    let _ ← IO.asTask (do IO.println "never"; (IO.Process.exit 4 : IO Unit))
  if args.headD "" == "exit" then
    let t ← IO.asTask (do IO.println "in task"; (IO.Process.exit 5 : IO Unit))
    let _ ← IO.wait t
  IO.println s!"gen {← gen s!"g{k}" b} {← gen k b}"
  IO.println "end"
