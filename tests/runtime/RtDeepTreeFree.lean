/-! Runtime test (memory): deep, one-sided binary trees freed whole, a type
with two recursive fields (`node l v r`). Natively the free is a loop over
objects linked through themselves, at any depth and on either side.
Modes, each a tree of N nodes:
- `tl N`, `tr N`: left-deep (`node t i leaf`) and right-deep
  (`node leaf i t`), in an `IO.Ref`, freed by `r.set` (a free that the
  runtime starts);
- `tlu N`, `tru N`: the same trees dropped by user code.
Arguments: MODE N (default: every mode, N = 1000). The peak memory is
checked by tests/runtime/alloc-check.sh (RtDeepTreeFree.alloc). -/

inductive T where
  | leaf
  | node (l : T) (v : Nat) (r : T)

def leftDeep (n : Nat) : T := Id.run do
  let mut t := T.leaf
  for i in [0:n] do t := .node t i .leaf
  return t

def rightDeep (n : Nat) : T := Id.run do
  let mut t := T.leaf
  for i in [0:n] do t := .node .leaf i t
  return t

/-- Takes a tree and gives `n` back; the tree is dropped by user code, here
or at the call. -/
@[noinline] def keep (p : T × Nat) : Nat := p.2

def top : T → Nat
  | .leaf => 0
  | .node _ v _ => v

def run (mode : String) (n : Nat) : IO Unit := do
  let mk := if mode.startsWith "tl" then leftDeep else rightDeep
  -- Through a reference, so that the tree is built before the print.
  let r ← IO.mkRef (mk n)
  let c ← r.get
  IO.println s!"{mode} {n}: {top c}"
  if mode.endsWith "u" then
    -- The reference gives the tree up; user code drops the last reference.
    r.set .leaf
    IO.println s!"kept {keep (c, n)}"
  else
    -- `c` is dead after the print: the reference holds the last reference,
    -- and its `set` frees the tree.
    r.set .leaf
    IO.println s!"freed {top (← r.get)}"

def main (args : List String) : IO Unit := do
  match args with
  | [mode, n] => run mode n.toNat!
  | _ => for m in ["tl", "tr", "tlu", "tru"] do run m 1000
