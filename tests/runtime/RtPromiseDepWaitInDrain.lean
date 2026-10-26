/-! Runtime test: Lean code that runs inside a free of a record type with
two recursive members (a promise's `sync` dependent) waits for a task, and
the task frees such a record and waits for a promise that record held.
`Tr` has two recursive fields. `main` drops a tree whose right child holds
the unresolved promise `pA`; freeing the child resolves `pA` with `none`,
and its `sync` dependent runs there and waits for task `tB` (which then
runs on the dependent's stack). `tB` drops a tree whose right grandchild
holds its own promise `q`, and waits for `q`'s result. Natively each free
is its own (`lean_del`'s to-do list is local to the call): `tB`'s drop
resolves `q` with `none`, and everything ends. A free whose pending work
is the thread's would take `tB`'s drop into `main`'s running free, which
resumes only after the dependent returns: `q` would never be resolved,
and the program would hang (the `.pipe` stops it after 20 s and prints the
exit code; natively Lean also warns on stderr that `Task.get` is called
from a `sync` task, so stderr is not compared). `consume` reads the tree
(its size), so Lean builds it and frees it there. -/

inductive Tr where
  | leaf : Tr
  | node : Tr → Option (IO.Promise Unit) → Tr → Tr

def Tr.size : Tr → Nat
  | .leaf => 0
  | .node l _ r => l.size + 1 + r.size

@[noinline] def consume (t : Tr) : IO Unit := do
  IO.println s!"size {t.size}"

@[noinline] def bBody : IO String := do
  let q ← IO.Promise.new (α := Unit)
  let r := q.result?
  consume (.node .leaf none (.node .leaf none (.node .leaf (some q) .leaf)))
  match ← IO.wait r with
  | none => pure "B: q dropped"
  | some _ => pure "B: q resolved"

def main : IO Unit := do
  let tB ← IO.asTask bBody
  let pA ← IO.Promise.new (α := Unit)
  let d ← IO.mapTask (sync := true) (fun (_ : Option Unit) => do
      IO.ofExcept (← IO.wait tB)) pA.result?
  consume (.node .leaf none (.node .leaf (some pA) .leaf))
  IO.println (← IO.ofExcept (← IO.wait d))
  IO.println "main: done"
