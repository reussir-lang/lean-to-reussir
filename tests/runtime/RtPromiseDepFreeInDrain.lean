/-! Runtime test: Lean code that runs inside a free of a record type with
two recursive members (a promise's `sync` dependent) frees such a record
itself. `Tr` has two recursive fields. `main` drops a tree whose right
child holds the unresolved promise `pA`; freeing the child resolves `pA`
with `none`, and its `sync` dependent runs there, inside that free. The
dependent drops a tree whose right grandchild holds its own promise `q`,
and then asks whether `q`'s result is finished. Natively each free is its
own (`lean_del`'s to-do list is local to the call): the dependent's drop
resolves `q` at once, so `true`. A free whose pending work is the
thread's would take the dependent's drop into the running free, and `q`
would be resolved only after the dependent returns (`false`). `consume`
reads the tree (its size), so Lean builds it and frees it there. -/

inductive Tr where
  | leaf : Tr
  | node : Tr → Option (IO.Promise Unit) → Tr → Tr

def Tr.size : Tr → Nat
  | .leaf => 0
  | .node l _ r => l.size + 1 + r.size

@[noinline] def consume (t : Tr) : IO Unit := do
  IO.println s!"size {t.size}"

def main : IO Unit := do
  let pA ← IO.Promise.new (α := Unit)
  let d ← IO.mapTask (sync := true) (fun (_ : Option Unit) => do
      let q ← IO.Promise.new (α := Unit)
      let r := q.result?
      consume (.node .leaf none (.node .leaf none (.node .leaf (some q) .leaf)))
      IO.println s!"dependent: q finished after its drop: {← IO.hasFinished r}") pA.result?
  consume (.node .leaf none (.node .leaf (some pA) .leaf))
  let _ ← IO.wait d
  IO.println "main: done"
