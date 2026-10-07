/-! Runtime test: `main : IO UInt32` whose exit code comes back from
polymorphic recursion (design review of the layout redesign, correctness,
DRC-01). `idPoly` calls itself at `α × α`, so the call goes to its uniform
instance, which returns the `UInt32` at `lcAny` (in an `L2RBox`); `main`
must unbox it and exit with code 7, as native does. -/
@[noinline] def idPoly {α : Type} : Nat → α → α
  | 0, x => x
  | n + 1, x => (idPoly n (x, x)).1

def main (args : List String) : IO UInt32 := do
  let k := (args.headD "3").toNat!
  let code := idPoly k (7 : UInt32)
  IO.println s!"code {code}"
  return code
