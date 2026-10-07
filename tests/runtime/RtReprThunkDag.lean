/-! Runtime test: a shared tree inside a forced thunk (blowup audit BA-04).
`build n` has n + 1 distinct nodes, each pointing twice to one child. The
thunk is forced, then packed once in an existential whose field is
`Thunk (Tree α)`: the uniform code needs a `Thunk (Tree lcAny)`, and
converting a forced thunk converts its value at once (the `done` case of
the lazy conversion), following every path: 2^(n+1) - 1 cells (4194302 at
n = 20; natively nothing is converted). The output is checked here; the
allocations by tests/runtime/alloc-check.sh (RtReprThunkDag.alloc). -/
inductive Tree (α : Type) where
  | leaf (x : α)
  | node (left right : Tree α)

@[noinline] def build : Nat → Tree Nat
  | 0 => .leaf 7
  | n + 1 => let t := build n; .node t t

structure LazyTree where
  α : Type
  t : Thunk (Tree α)

@[noinline] def leftDepth (p : LazyTree) : Nat := go p.t.get
where
  go {α : Type} : Tree α → Nat
    | .leaf _ => 0
    | .node l _ => 1 + go l

def main (args : List String) : IO Unit := do
  let n := (args.headD "16").toNat!
  let t : Thunk (Tree Nat) := Thunk.mk fun _ => build n
  match t.get with
  | .node .. => IO.println (leftDepth ⟨Nat, t⟩)
  | .leaf _ => IO.println 0
