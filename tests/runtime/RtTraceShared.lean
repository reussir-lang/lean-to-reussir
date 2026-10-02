inductive E where
  | ok (n : Nat) (s : String)
  | err (s : String) (k : Nat)
  deriving Inhabited

@[noinline] def mk (n : Nat) : Array E := #[E.err s!"boom{n}" n, E.ok n "a"]

@[noinline] def pick (xs : Array E) (i : Nat) : E := xs[i]!

@[noinline] def step (xs : Array E) (i : Nat) : E :=
  match pick xs i with
  | .err s k => .err s k
  | .ok n s => .ok (n+1) s

def main (args : List String) : IO Unit := do
  let xs := mk args.length
  let r := step xs 0
  let r := dbgTraceIfShared "r" r
  match r with
  | .err s k => IO.println s!"err {s} {k} {xs.size}"
  | .ok n s => IO.println s!"ok {n} {s} {xs.size}"
