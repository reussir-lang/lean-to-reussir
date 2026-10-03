/-! Runtime test: `Task.map (sync := true)` of a finished task applies `f`
at once in the calling thread (its `dbgTrace` goes into `main`'s redirected
stderr, where an ordinary pure task's goes to the process's); a task
converted to another representation is the original task for the runtime
while it is forced through that handle (`IO.cancel` through it reaches the
running task); a
bind task whose `f` returns a finished task finishes at once, so its
dependents are enqueued then, before later tasks. -/

@[noinline] def hn (x : Nat) : Nat := x

structure SC where
  run : {β : Type} → IO.Ref (Option (IO Unit)) → IO.Ref (Option (IO String)) → Task β → IO Unit

@[noinline] def mkSC (k : Nat) : SC := if k > 100 then ⟨fun _ _ t => do let _ ← IO.wait t⟩ else
  ⟨fun r r2 t => do
    r.set (some (IO.cancel t))
    r2.set (some (do return s!"{repr (← IO.getTaskState t)} {← IO.hasFinished t}"))
    let _ ← IO.wait t
    IO.println s!"after wait in uniform code: {repr (← IO.getTaskState t)}"⟩

def main (args : List String) : IO Unit := do
  let k := args.length
  -- sync map in the calling thread
  let re ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let olde ← IO.setStderr (IO.FS.Stream.ofBuffer re)
  let t : Task Nat := Task.pure (hn (k + 1))
  let m := t.map (sync := true) fun x => dbgTrace s!"sync map {x}" fun _ => x + 1
  let m2 := t.map fun x => dbgTrace s!"async map {x}" fun _ => x + 2
  IO.println s!"{m.get} {m2.get}"
  let _ ← IO.setStderr olde
  IO.println s!"main stderr buffer {(String.fromUTF8! (← re.get).data).quote}"
  -- cancel through a converted handle while it is forced
  let r : IO.Ref (Option (IO Unit)) ← IO.mkRef none
  let r2 : IO.Ref (Option (IO String)) ← IO.mkRef none
  let c ← IO.asTask (do
    IO.sleep 10
    if let some f := ← r.get then f
    if let some g := ← r2.get then IO.println s!"inside: state {← g}"
    IO.println s!"inside: canceled {← IO.checkCanceled}"
    return hn 1)
  (mkSC k).run r r2 c
  IO.println s!"done {repr (← IO.getTaskState c)}"
  -- bind of a finished task at exit
  let b0 ← IO.asTask (do IO.sleep 50; IO.println "t"; return hn 1)
  let b ← IO.bindTask b0 (fun _ => do
    IO.println "f"
    let _ ← IO.asTask (do IO.println "q"; let _ ← IO.asTask (IO.println "v"))
    return Task.pure (.ok (hn 2)))
  let _ ← IO.mapTask (fun r => IO.println s!"m {r.toOption}") b
  IO.println "main returns"
