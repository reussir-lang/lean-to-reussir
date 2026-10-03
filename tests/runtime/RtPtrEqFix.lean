/-! Runtime test: code that stops when `ptrEq` says a step changed nothing
(the `Expr.replace` idiom, fixpoint loops) over values a match arm returns
whole (adv3 RP3-1/RP3-2), a traversal keeping unchanged nodes of a DAG, a
lookup returning a node, and `ptrEq` on `[value]` one-field structures.
lean2rr does not emulate native pointer identity (translation plan §9), so
only results that do not depend on it are printed: the values the
fixpoints reach, not their number of steps or `ptrEq` itself. -/

inductive L where
  | nil
  | cons (h : Nat) (t : L)

def L.ofList : List Nat → L
  | [] => .nil
  | x :: xs => .cons x (L.ofList xs)

def L.len : L → Nat
  | .nil => 0
  | .cons _ t => t.len + 1

@[noinline] def dropZeros : L → L
  | .cons 0 t => dropZeros t
  | l => l

unsafe def fixDrop (l : L) (n : Nat) : L :=
  if n > 50 then l else
  let l' := dropZeros l
  if ptrEq l l' then l else fixDrop l' (n + 1)

inductive Tr where
  | leaf
  | node (l : Tr) (k : Nat) (r : Tr)

def Tr.ins : Tr → Nat → Tr
  | .leaf, x => .node .leaf x .leaf
  | .node l k r, x => if x < k then .node (l.ins x) k r else if k < x then .node l k (r.ins x) else .node l k r

def Tr.sub : Tr → Nat → Tr
  | .leaf, _ => .leaf
  | .node l k r, x => if x < k then l.sub x else if k < x then r.sub x else .node l k r

def Tr.size : Tr → Nat
  | .leaf => 0
  | .node l _ r => l.size + 1 + r.size

@[noinline] def mkTree (n : Nat) : Tr := (List.range n).foldl (fun t i => t.ins ((i * 7919) % n)) .leaf

@[noinline] def rootKey : Tr → Nat
  | .leaf => 0
  | .node _ k _ => k

@[noinline] def rightOf : Tr → Tr
  | .leaf => .leaf
  | .node _ _ r => r

inductive E where
  | num (n : Nat)
  | add (a b : E)
  | neg (a : E)

def E.toStr : E → String
  | .num n => toString n
  | .add a b => s!"({a.toStr}+{b.toStr})"
  | .neg a => s!"-{a.toStr}"

unsafe def E.simp1 (e : E) : E :=
  match e with
  | .neg (.neg a) => a.simp1
  | .add a b =>
    let a' := a.simp1
    let b' := b.simp1
    if ptrEq a a' && ptrEq b b' then e else .add a' b'
  | .neg a =>
    let a' := a.simp1
    if ptrEq a a' then e else .neg a'
  | .num _ => e

unsafe def E.fix (e : E) (n : Nat) : E :=
  if n > 50 then e else
  let e' := e.simp1
  if ptrEq e e' then e else E.fix e' (n + 1)

def E.count : E → Nat
  | .num _ => 1
  | .add a b => a.count + b.count + 1
  | .neg a => a.count + 1

def E.dag : Nat → E
  | 0 => .num 1
  | n+1 => let d := E.dag n; .add d d

-- A one-field recursive structure ([value] in lean2rr) and one over a String.
inductive R where
  | mk (xs : Array R)

@[noinline] def keepR (r : R) : R := match r with
  | .mk xs => if xs.size > 100 then .mk #[] else r

def R.size : R → Nat
  | .mk xs => xs.attach.foldl (fun n ⟨x, _⟩ => n + x.size) 1

unsafe def fixR (r : R) (n : Nat) : R :=
  if n > 20 then r else
  let r' := keepR r
  if ptrEq r r' then r else fixR r' (n + 1)

structure W where
  s : String

@[noinline] def keepW (w : W) : W := if w.s.length > 100 then ⟨""⟩ else w

unsafe def main (args : List String) : IO Unit := do
  let k := args.length
  IO.println s!"fixDrop: {(fixDrop (L.ofList [0, 0, 5, 6, k]) 0).len}"
  let l := L.ofList [3, 4 + k]
  IO.println s!"dropZeros: {(dropZeros l).len}"
  let t := mkTree (100 + k)
  let t2 := t.ins (rootKey t)
  IO.println s!"ins present key: {t2.size}"
  let t3 := t.sub (rootKey (rightOf t))
  IO.println s!"sub: {t3.size} {(rightOf t).size}"
  let e := E.add (.neg (.neg (.num 1))) (.add (.num (2 + k)) (.neg (.num 3)))
  IO.println s!"simp fix: {(E.fix e 0).toStr}"
  let d := E.dag (18 + k)
  IO.println s!"dag: {d.simp1.count}"
  IO.println s!"value struct: {(fixR (.mk #[.mk #[]]) 0).size}"
  let w : W := ⟨s!"w{k}"⟩
  IO.println s!"value struct over String: {(keepW w).s} {!ptrEq w (keepW w) || (keepW w).s == w.s}"
