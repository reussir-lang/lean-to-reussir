/-! Runtime test: an `initialize` reference, which native Lean marks
persistent right after its initializer (`lean_mark_persistent`, while it
holds `none`), later holds an unresolved promise; then a closed term that
reaches the reference is evaluated (`lean_obj_once`, marked persistent at
its first evaluation). Native's walk does not look into an object that is
persistent already, so it does not wait for the promise: `main` goes on and
resolves the promise itself. Once lean2rr's walk waited for promises
(HTSK2-02), without a persistent mark, it read the reference's current
value and waited for the promise, and the program hung (review RV-01 of
HTSK2-02; `NAME.pipe` stops a hang after 20 s). -/
initialize globalRef : IO.Ref (Option (IO.Promise Nat)) ← IO.mkRef none

@[noinline] def getPair (_ : Unit) : IO.Ref (Option (IO.Promise Nat)) × String := (globalRef, "pair")

def main (args : List String) : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  globalRef.set (some p)
  let pr := getPair ()
  IO.println s!"main: {pr.2}"
  p.resolve args.length
  IO.println s!"main: {p.result?.get}"
