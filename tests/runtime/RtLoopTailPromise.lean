/-! Runtime test (leanrt hunt after D8, H3): `for` loops whose body makes,
resolves and tests promises stay loops. The prelude's promise textures lent
their locals to leanrt functions that are not inlined
(`task::promise_cell(&p)`, also in `isResolved`'s texture, and
`task::resolve_with` with a closure over the texture's locals);
inlined into the loop's function, the escaping stack slot kept the loop's
self tail call a real call (see "An escaping stack slot blocks tail calls"
in the workaround docs), and 2*10^7 steps overflowed the stack (1 GB) where
native Lean runs in 8 MB. The textures now call by-value wrappers
(`task::owned`). Runs 2*10^5 steps on a 1 MiB stack (`.pipe`). -/

def main (args : List String) : IO Unit := do
  let n := (args.headD "10").toNat!
  -- a fresh promise per step, resolved, tested and read
  let mut acc := 0
  for k in [0:n] do
    let p ← IO.Promise.new (α := Nat)
    p.resolve k
    if ← p.isResolved then
      acc := (acc + p.result!.get) % 1000003
  IO.println s!"resolve: acc={acc}"
  -- one resolved promise tested at every step
  let q ← IO.Promise.new (α := Nat)
  q.resolve 5
  let mut acc2 := 0
  for k in [0:n] do
    if ← q.isResolved then
      acc2 := (acc2 + k) % 1000003
  IO.println s!"isResolved: acc={acc2}"
  -- the promise code is in the loop but runs only once
  let mut acc3 := 0
  for k in [0:n] do
    if k == 7 then
      let p ← IO.Promise.new (α := Nat)
      p.resolve k
      acc3 := acc3 + p.result!.get
    acc3 := (acc3 + k) % 1000003
  IO.println s!"once: acc={acc3}"
