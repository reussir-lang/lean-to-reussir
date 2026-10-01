/-! Runtime test: dropping deep values (`RtDropDeep.pipe` runs it at an
8 MB stack, `LEAN_STACK_SIZE_KB=8192`). Native Lean frees iteratively; the
runtime's containers (arrays, thunk and task cells, references) free their
last reference through a stack of pending work (`leanrt::drop`), so a
value deep through containers, with records in between, does not use stack
per level: a tree whose children are in arrays (typed and in uniform code),
a record → array → record chain, a chain of forced thunks, a chain of
mapped tasks. -/

inductive ATree | node (v : Nat) (kids : Array ATree)
mutual
inductive MA | mk (v : Nat) (xs : Array MB)
inductive MB | leaf | mk (a : MA) (w : String)
end
inductive TC | nil | cons (v : Nat) (t : Thunk TC)
inductive UT (α : Type) | node (x : α) (kids : Array (UT α))
structure G where
  α : Type
  x : α

@[noinline] def mkATree (n : Nat) : ATree := Id.run do
  let mut acc : ATree := .node 0 #[]
  for i in [0:n] do acc := .node (i % 3) #[.node 1 #[], acc]
  return acc
@[noinline] def mkMA (n : Nat) : MA := Id.run do
  let mut acc : MA := .mk 0 #[]
  for i in [0:n] do acc := .mk i #[.leaf, .mk acc "x"]
  return acc
@[noinline] def mkTC (n : Nat) : TC := Id.run do
  let mut acc : TC := .nil
  for i in [0:n] do
    let prev := acc
    let t : Thunk TC := Thunk.mk fun _ => prev
    let _ := t.get
    acc := .cons i t
  return acc
@[noinline] def mkUT {α : Type} (x : α) (n : Nat) : UT α := Id.run do
  let mut acc : UT α := .node x #[]
  for _ in [0:n] do acc := .node x #[.node x #[], acc]
  return acc
@[noinline] def mkTasks (n : Nat) : Task Nat := Id.run do
  let mut t : Task Nat := Task.pure 0
  for i in [0:n] do t := t.map (· + i % 2)
  return t

@[noinline] def topA : ATree → Nat | .node v _ => v
@[noinline] def topM : MA → Nat | .mk v _ => v
@[noinline] def topT : TC → Nat | .nil => 0 | .cons v _ => v
@[noinline] def uarr (g : G) (n : Nat) : Nat := match mkUT g.x n with | .node _ ks => ks.size

def main : IO Unit := do
  let n := 1000000
  IO.println s!"arrays {topA (mkATree n)}"
  IO.println s!"mixed {topM (mkMA n)}"
  IO.println s!"thunks {topT (mkTC n)}"
  IO.println s!"uniform arrays {uarr ⟨Nat, 3⟩ n}"
  IO.println s!"tasks {(mkTasks 200000).get}"
