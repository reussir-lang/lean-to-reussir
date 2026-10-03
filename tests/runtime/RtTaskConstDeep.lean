/-! Runtime test: a top-level constant whose value is a chain of 300000 cells,
each holding a task, linked through the first field. Natively
`lean_mark_persistent` walks it with an explicit stack when the constant is
initialized; lean2rr's traversal (`l2r_persist_T`) must not recurse once per
cell.
From the round-7 review, area L (rv7/lowering), finding RV7L-01, repro
LwPersistMin. -/

-- A constant (CAF) whose value is a chain of 300000 cells, each holding a task,
-- linked through the first field. Natively lean_mark_persistent walks it with
-- an explicit stack; lean2rr's l2r_persist_T recurses on every non-last field.
inductive Chain where
  | nil
  | link (prev : Chain) (job : Task Nat)

def mkChain (n : Nat) : Chain := Id.run do
  let mut c := Chain.nil
  for i in [0:n] do c := .link c (Task.pure i)
  return c

def jobs : Chain := mkChain 300000

def main : IO Unit := do
  match jobs with
  | .link _ t => IO.println s!"last job {t.get}"
  | .nil => IO.println "empty"

