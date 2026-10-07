/-! Runtime test (hunt HSK-01, switch step 16): nested waits under deep
recursion. `D K`: `main` recurses `D` levels, then waits for a new task
that recurses `D` levels and waits for the next one, `K` tasks deep, with
`Task.get` (`chain`) and with `IO.wait` (`chainio`). Natively each awaited
task runs on a worker thread of its own, with a whole stack
(`LEAN_STACK_SIZE_KB=16384` here). lean-runtime's single-thread scheduler
ran each awaited task on its waiter's stack, so the recursions added up on
one stack and the program overflowed; since lean-runtime's fixes-16 a task
runs there only with a native worker's room left, and otherwise on a
context of its own. -/

-- Non-tail recursion: `d` levels, then the wait for a new task that does
-- the same `top` levels with one level of chain less.
partial def descend (top : Nat) (d k : Nat) : Nat :=
  if d == 0 then
    if k == 0 then 0 else (Task.spawn fun _ => descend top top (k - 1)).get + 1
  else descend top (d - 1) k * 3 % 1000003 + 1

-- The same with IO tasks.
partial def descendIO (top : Nat) (d k : Nat) : IO Nat := do
  if d == 0 then
    if k == 0 then return 0
    let t ← IO.asTask (descendIO top top (k - 1))
    match ← IO.wait t with
    | .ok v => return v + 1
    | .error e => throw e
  else
    let r ← descendIO top (d - 1) k
    return r * 3 % 1000003 + 1

def main (args : List String) : IO Unit := do
  let d := (args[0]?.bind String.toNat?).getD 1000
  let k := (args[1]?.bind String.toNat?).getD 2
  IO.println s!"chain {descend d d k}"
  IO.println s!"chainio {← descendIO d d k}"
