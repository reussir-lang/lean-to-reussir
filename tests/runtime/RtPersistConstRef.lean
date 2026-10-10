/-! Runtime test: as RtPersistInitRef, with a constant made by unsafe IO
instead of an `initialize` declaration. Natively the module initializer
evaluates the constant and marks it persistent while the reference holds
`none`; the closed term evaluated later does not look into the reference,
so `main` resolves the promise itself. Once lean2rr's walk waited for
promises, without a persistent mark, the program hung (review RV-01 of
HTSK2-02; `NAME.pipe` stops a hang after 20 s). -/
def globalRef : IO.Ref (Option (IO.Promise Nat)) := unsafe unsafeBaseIO (IO.mkRef none)

@[noinline] def getPair (_ : Unit) : IO.Ref (Option (IO.Promise Nat)) × String := (globalRef, "pair")

def main (args : List String) : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  globalRef.set (some p)
  let pr := getPair ()
  IO.println s!"main: {pr.2}"
  p.resolve args.length
  IO.println s!"main: {p.result?.get}"
