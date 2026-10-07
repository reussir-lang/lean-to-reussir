/-! Runtime test: a shared tree converted between two specialized layouts,
with no uniform code (blowup audit BA-05). One generic function builds a
tree of `none`s at two element types; Lean's mono-phase `cse` merges the
two calls (their erased arguments agree), so lean2rr calls one instance and
converts its result to the other (`Tree (Option Nat)` to
`Tree (Option String)`, Mono.lean's merges of erased type arguments). The
tree has n + 1 distinct nodes; a conversion that follows every path builds
2^(n+1) - 1 cells (5242878 cells at n = 20; natively nothing is converted).
The output is checked here; the allocations by
tests/runtime/alloc-check.sh (RtReprCseDag.alloc). -/
inductive Tree (α : Type) where
  | leaf (x : α)
  | node (left right : Tree α)

@[noinline] def sharedTree {α : Type} : Nat → Tree (Option α)
  | 0 => .leaf none
  | n + 1 => let t := sharedTree n; .node t t

@[noinline] def leftDepth {α : Type} : Tree α → Nat
  | .leaf _ => 0
  | .node l _ => 1 + leftDepth l

@[noinline] def rightDepth {α : Type} : Tree α → Nat
  | .leaf _ => 0
  | .node _ r => 1 + rightDepth r

def main (args : List String) : IO Unit := do
  let n := (args.headD "16").toNat!
  let a : Tree (Option Nat) := sharedTree n
  let b : Tree (Option String) := sharedTree n
  IO.println (leftDepth a + rightDepth b)
