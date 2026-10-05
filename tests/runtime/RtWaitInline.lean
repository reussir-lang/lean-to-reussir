/-! Runtime test, and the program of `wait-inline-check.sh`: in a program that
creates tasks, a loop of reference operations (`get`, `set`, `swap`,
`modify`) and a loop forcing thunks. The check reads the executable's
machine code: the reference points, a thunk's store (`l2r_lcell_set`) and
its wake of waiters (lean-runtime's `done_keyed`) are inline in the loops,
their thread-local loads direct, and only the slow paths are calls. -/

def refLoop (r : IO.Ref Nat) : Nat → IO Unit
  | 0 => pure ()
  | n + 1 => do
    let v ← r.get
    r.set (v + 1)
    let w ← r.swap (v + 2)
    r.modify (· + w)
    refLoop r n

@[noinline] def mkThunks (n : Nat) : Array (Thunk Nat) :=
  (Array.range n).map fun i => Thunk.mk fun _ => i * 3 + 1

def sumThunks (ts : Array (Thunk Nat)) : Nat :=
  ts.foldl (fun s t => s + t.get) 0

def main : IO Unit := do
  let t ← IO.asTask (pure 7)
  let r ← IO.mkRef 0
  refLoop r 1000
  let ts := mkThunks 1000
  IO.println s!"reference: {← r.get}, thunks: {sumThunks ts} {sumThunks ts}"
  match t.get with
  | .ok v => IO.println s!"task: {v}"
  | .error e => IO.println s!"task: {e}"
