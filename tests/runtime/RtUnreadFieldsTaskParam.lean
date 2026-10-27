/-!
Runtime test of the optimization `unread-fields` (off by default; this
test turns it on, `RtUnreadFieldsTaskParam.enable-opts`) in a program that
creates tasks. There, a value is replaced only when it cannot hold a task,
nor can the values a closure captured: natively an initializer's value is
marked persistent, which reaches every task the value holds, also a task
that a closure captured.
- `keepA`: a task in a field no code reads (`Keep.keep`, of type `Task`,
  which the pass never replaces).
- `cfgB`: the closure `adder t`, in a field that `main` applies, captured
  the task `t` at a parameter that `adder` does not use. The pass keeps
  the argument (bug hunt of the pass, S1: an argument at an unused
  parameter of a partial application became a placeholder).
Before `main` both sides run a task when it is made (no task manager
yet), so the output is the same with the argument replaced; the
`.l2r-debug` line pins the pass's decision: one captured argument kept.
-/

@[noinline] def adder (_t : Task Nat) (n : Nat) : Nat := n + 1

structure Keep where
  name : String
  keep : Task Nat
deriving Nonempty

structure Cfg where
  name : String
  run : Nat → Nat
deriving Nonempty

-- A number known only at run time, so that a task is not a closed term.
def runtimeK : IO Nat := do
  return if (← IO.getEnv "L2R_NO_SUCH_VAR").isSome then 1 else 2

-- The task captured by a closure at a parameter the function does not use.
initialize cfgB : Cfg ← do
  let k ← runtimeK
  let t := Task.spawn fun _ => dbgTrace s!"pure task B {k}" fun _ => k + 20
  pure { name := "b", run := adder t }

-- The task in a field no code reads (the pass keeps it).
initialize keepA : Keep ← do
  let k ← runtimeK
  let t := Task.spawn fun _ => dbgTrace s!"pure task A {k}" fun _ => k + 10
  pure { name := "a", keep := t }

def main : IO Unit := do
  IO.eprintln "main starts"
  IO.println s!"{keepA.name} {cfgB.name} {cfgB.run 3}"
