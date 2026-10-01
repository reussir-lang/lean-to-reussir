/-! Runtime test: deep values converted to another representation (plan
§5.1): structural conversions run in loops, not one stack frame per level,
so they do not overflow at an 8 MB stack (`RtConvDeep.pipe`) where native
Lean, which converts nothing, does not. A list (recursive field last or
first), a tree deep in its first or last child, a list of lists, a list of
pairs, mutual inductives; and `Array.mk` / `String.mk` / `String.ofList` of
long lists. -/

structure PkgL where
  α : Type
  l : List α

inductive RL (α : Type) | nil | cons (t : RL α) (h : α)
inductive TL (α : Type) | leaf | node (l : TL α) (v : α) (r : TL α)
mutual
inductive Ev (α : Type) | zero (v : α) | succ (o : Od α)
inductive Od (α : Type) | succ (e : Ev α) (v : α)
end

structure PkgRL where
  α : Type
  l : RL α
structure PkgTL where
  α : Type
  t : TL α
structure PkgLL where
  α : Type
  l : List (List α)
structure PkgLP where
  α : Type
  l : List (α × String)
structure PkgE where
  α : Type
  t : Ev α

@[noinline] def mkList (n : Nat) : List Nat := (List.range n).map (· % 7)
@[noinline] def mkRL (n : Nat) : RL Nat := Id.run do
  let mut acc : RL Nat := .nil
  for i in [0:n] do acc := .cons acc (i % 5)
  return acc
@[noinline] def mkRight (n : Nat) : TL Nat := Id.run do
  let mut acc : TL Nat := .leaf
  for i in [0:n] do acc := .node .leaf (i % 5) acc
  return acc
@[noinline] def mkLeft (n : Nat) : TL Nat := Id.run do
  let mut acc : TL Nat := .leaf
  for i in [0:n] do acc := .node acc (i % 5) .leaf
  return acc
@[noinline] def mkEv (n : Nat) : Ev Nat := Id.run do
  let mut acc : Ev Nat := .zero 7
  for i in [0:n] do acc := .succ (.succ acc (i % 2))
  return acc

def RL.sum : RL Nat → Nat → Nat
  | .nil, a => a
  | .cons t h, a => t.sum (a + h)
partial def TL.sumSpine : TL Nat → Nat → Nat
  | .leaf, a => a
  | .node .leaf v r, a => r.sumSpine (a + v)
  | .node l v .leaf, a => l.sumSpine (a + v)
  | .node _ v _, a => a + v
def Ev.sum (e : Ev Nat) : Nat := Id.run do
  let mut cur := e
  let mut s := 0
  for _ in [0:100000000] do
    match cur with
    | .zero v => s := s + v; break
    | .succ (.succ e v) => s := s + v; cur := e
  return s

@[noinline] unsafe def sumL (p : PkgL) : Nat := (unsafeCast p.l : List Nat).foldl (· + ·) 0
@[noinline] unsafe def sumRL (p : PkgRL) : Nat := (unsafeCast p.l : RL Nat).sum 0
@[noinline] unsafe def sumTL (p : PkgTL) : Nat := (unsafeCast p.t : TL Nat).sumSpine 0
@[noinline] unsafe def sumLL (p : PkgLL) : Nat := (unsafeCast p.l : List (List Nat)).foldl (fun a l => a + l.length) 0
@[noinline] unsafe def sumLP (p : PkgLP) : Nat := (unsafeCast p.l : List (Nat × String)).foldl (fun a (x, _) => a + x) 0
@[noinline] unsafe def sumE (p : PkgE) : Nat := (unsafeCast p.t : Ev Nat).sum

unsafe def main : IO Unit := do
  let n := 1000000
  IO.println s!"list {sumL ⟨Nat, mkList n⟩}"
  IO.println s!"snoc {sumRL ⟨Nat, mkRL n⟩}"
  IO.println s!"right {sumTL ⟨Nat, mkRight n⟩}"
  IO.println s!"left {sumTL ⟨Nat, mkLeft n⟩}"
  IO.println s!"lists {sumLL ⟨Nat, (List.range n).map fun i => [i]⟩}"
  IO.println s!"pairs {sumLP ⟨Nat, (List.range n).map fun i => (i % 3, "s")⟩}"
  IO.println s!"mutual {sumE ⟨Nat, mkEv n⟩}"
  let a := Array.mk (mkList (4 * n))
  IO.println s!"Array.mk {a.size} {a.foldl (· + ·) 0}"
  let cs := (List.range (4 * n)).map fun i => Char.ofNat (97 + i % 26)
  IO.println s!"String.mk {(String.mk cs).length} ofList {(String.ofList cs).length}"
