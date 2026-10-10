/-! Runtime test: as RtPersistConstRefPromise, with an unfinished task in
the constant reference instead of a promise. Natively the closed term's
walk does not look into the reference, persistent since the module
initializer: `main` prints its lines first and sees the task unfinished.
lean2rr walked the constant at startup only when a task was unfinished
(never, at startup) and kept no mark between walks, so the closed term's
walk read the reference and waited for the task: "task: done" came first
and `main` saw it finished (review RV-01 of HTSK2-02). -/
def globalRef : IO.Ref (Option (Task Nat)) := unsafe unsafeBaseIO (IO.mkRef none)

@[noinline] def getPair (_ : Unit) : IO.Ref (Option (Task Nat)) × String := (globalRef, "pair")

def main (args : List String) : IO Unit := do
  let t ← IO.asTask (prio := .dedicated) do
    IO.sleep 200
    IO.println "task: done"
    pure args.length
  globalRef.set (some (t.map fun r => match r with | .ok v => v | .error _ => 0))
  let pr := getPair ()
  IO.println s!"main: {pr.2}"
  let fin ← IO.hasFinished t
  IO.println s!"main: finished {fin}"
  let _ ← IO.wait t
