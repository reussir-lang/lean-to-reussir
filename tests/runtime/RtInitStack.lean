/-! Runtime test: module initializers run on the process's main thread
(its usual 8 MiB stack), not on Lean's big main-program thread: a deep
non-tail recursion in an initializer overflows (`Stack overflow detected.
Aborting.`, exit 134), while the same depth in `main` is fine. -/

def deep : Nat → Nat
  | 0 => 0
  | n + 1 => deep n + 1

def depth : IO Nat := do
  -- Not a compile-time constant.
  let t ← IO.monoNanosNow
  return 3000000 + (if t == 0 then 1 else 0)

initialize gDeep : Nat ← do
  IO.println "initializing"
  return deep (← depth)

def main : IO Unit := do
  IO.println s!"main {gDeep} {deep (← depth)}"
