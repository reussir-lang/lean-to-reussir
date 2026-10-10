/-! Runtime test: a constant reference (made by unsafe IO; natively
evaluated and marked persistent at module initialization, while it holds
`none`) that later holds an unresolved promise, which a dedicated task
resolves after 200 ms; a closed term that reaches the reference is
evaluated meanwhile. Native's walk does not look into the persistent
reference, so `main` prints its lines before the resolver's. Once lean2rr's
walk waited for promises, without a persistent mark, it waited for the
resolver first (review RV-01 of HTSK2-02). -/
def globalRef : IO.Ref (Option (IO.Promise Nat)) := unsafe unsafeBaseIO (IO.mkRef none)

@[noinline] def getPair (_ : Unit) : IO.Ref (Option (IO.Promise Nat)) × String := (globalRef, "pair")

def main (args : List String) : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  globalRef.set (some p)
  let _ ← IO.asTask (prio := .dedicated) do
    IO.sleep 200
    IO.println "resolver: resolving"
    p.resolve args.length
  let pr := getPair ()
  IO.println s!"main: {pr.2}"
  let fin ← IO.hasFinished p.result?
  IO.println s!"main: resolved {fin}"
  let _ ← IO.wait p.result?
