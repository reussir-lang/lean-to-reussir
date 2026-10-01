/-! Runtime test: a stack overflow prints `Stack overflow detected.
Aborting.` and aborts (exit 134, buffered stdout lost) in every thread
that runs Lean code: `main`'s thread (Lean's 1 GiB, a smaller
`LEAN_STACK_SIZE_KB`, or the process's thread with `LEAN_MAIN_USE_THREAD=0`),
tasks, the process's main thread while initializers and constants run, and
a task an initializer starts; also when the overflow happens inside GMP,
whose scratch space is on the stack. `RtStackOverflow.pipe` runs each case;
`RT_OVERFLOW` picks the startup ones. -/

-- Non-tail recursion that allocates nothing.
def deep : Nat → Nat
  | 0 => 0
  | n + 1 => deep n * 3 % 1000003 + 1

partial def spin (n : Nat) : Nat := if n == 7 then 0 else spin (n + 2) + 1

-- A GMP multiplication and division at every level.
def deepBig (m : Nat) : Nat → Nat → Nat
  | 0, x => x % 1000
  | n + 1, x =>
    let y := x * x % m
    deepBig m n y + 1

def overflowAt (what : String) : Bool :=
  (unsafe unsafeBaseIO (IO.getEnv "RT_OVERFLOW")) == some what

def overflowConst : Nat := if overflowAt "caf" then deep 100000000 else 0

initialize initValue : Nat ← do
  if overflowAt "init" then
    IO.println "initializer runs"
    return deep 100000000
  if overflowAt "inittask" then
    let t ← IO.asTask (do let k ← IO.getNumHeartbeats; pure (deep (100000000 + k)))
    return (← IO.wait t).toOption.getD 0
  return 0

def main (args : List String) : IO UInt32 := do
  IO.println s!"before {overflowConst} {initValue}"
  let n := (args[1]?.bind String.toNat?).getD 1000000000
  match args[0]? with
  | some "main" => IO.println s!"{deep n}"
  | some "spin" => IO.println s!"{spin 0}"
  | some "task" =>
    let t ← IO.asTask (do let k ← IO.getNumHeartbeats; pure (deep (n + k)))
    IO.println s!"{(← IO.wait t).toOption}"
  | some "spawn" => IO.println s!"{(Task.spawn fun _ => deep n).get}"
  | some "dedicated" =>
    let t ← IO.asTask (prio := .dedicated) (do let k ← IO.getNumHeartbeats; pure (deep (n + k)))
    IO.println s!"{(← IO.wait t).toOption}"
  | some "pure" => IO.println s!"{(Task.spawn (prio := .dedicated) fun _ => spin 0).get}"
  | some "big" =>
    let e := 60000
    IO.println s!"{deepBig (2 ^ e + 7) n (2 ^ (e - 3) + 12345)}"
  | _ => IO.println s!"no overflow"
  return 0
