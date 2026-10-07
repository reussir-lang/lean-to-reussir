/-! Runtime test: `dbgTraceIfShared` sees the caller's record shared where
a loop returns it at once (review of optimization `flatten-structs`, round
4, F1 and F2): through a function value (`viaFn`), and in a peeled loop's
first step, which the wrapper runs on the caller's record (`outerT` gives
`inner`'s result to `report`). Natively both messages are printed; a
rebuilt copy is not shared. -/
structure P where
  a : Nat
  b : Nat
  deriving Inhabited

@[noinline] def run (p : P) : List Nat → P
  | [] => p
  | x :: xs => run ⟨p.a + x, p.b + 1⟩ xs

@[noinline] def fromFresh (n : Nat) (xs : List Nat) : Nat := (run ⟨n, n⟩ xs).a

@[noinline] def viaFn (f : P → List Nat → P) (p : P) : P := f p []

@[noinline] def inner (p : P) : Nat → P
  | 0 => p
  | k+1 => inner ⟨p.a + 1, p.b⟩ k

@[noinline] def innerA (k : Nat) : Nat := (inner ⟨k, k⟩ k).a

@[noinline] def report (t : P) : Nat := (dbgTraceIfShared "t shared" t).b

-- peeled (s stored at the exit); the first step gives inner's result to report
@[noinline] def outerT (s : P) (k : Nat) : Nat → Array P → Array P
  | 0, acc => acc.push s
  | n+1, acc =>
    let t := inner s k
    let r := report t
    outerT ⟨t.a + r, t.b + 1⟩ k n acc

def main (args : List String) : IO Unit := do
  let b0 : P := ⟨args.length + 7, 1⟩
  let r := viaFn run b0
  let r' := dbgTraceIfShared "r shared" r
  IO.println s!"viaFn {r'.a} {b0.b} {fromFresh 2 [3]}"
  let acc := outerT b0 0 1 #[]
  IO.println s!"outerT {acc.size} {b0.a} {innerA 2}"
