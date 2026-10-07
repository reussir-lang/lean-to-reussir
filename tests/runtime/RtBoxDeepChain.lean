/-! Runtime test: a chain of 10^6 nested boxes (each `T.node`'s array holds
a box of the next node) freed on a 1 MiB stack (`LEAN_STACK_SIZE_KB=1024`
for both builds, in `RtBoxDeepChain.pipe`), by an array set (outside a
free) and by a reference set: the last release of each box's payload goes
on the pending stack as one cell (`any::release_last`: the payload's
cell, with the program's release of its type), so the free uses no stack
per level (review of the deferral of a box's word, 22bcf89; the cell
itself since the release table). -/

inductive T where
  | leaf
  | node (c : Array T) (k : Nat)

def build : Nat → T → T
  | 0, acc => acc
  | n + 1, acc => build n (.node #[acc] n)

partial def depth : T → Nat → Nat
  | .leaf, d => d
  | .node c _, d => match c[0]? with
    | some t => depth t (d + 1)
    | none => d

@[noinline] def setAt (arr : Array T) (i : Nat) (x : T) : Array T := arr.set! i x

def main : IO Unit := do
  let t := build 1000000 .leaf
  IO.println s!"depth {depth t 0}"
  let arr := setAt #[t] 0 .leaf
  IO.println s!"after the set ({arr.size})"
  let r ← IO.mkRef (build 1000000 .leaf)
  r.set .leaf
  IO.println "after the reference set"
