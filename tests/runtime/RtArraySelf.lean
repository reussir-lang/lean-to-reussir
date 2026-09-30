/-! Runtime test: types holding arrays of themselves (adv3 RP3-6). `Array T`
inside `T`'s own fields has the representation `Array T` has everywhere
else (a shared record's array is `RVec<T>`), so reading, pushing or folding
the field does not convert the whole array (it used to: O(size) per access,
quadratic building). Covers a rose tree, a structure over its own array,
mutual types used in either order, and one-field types (`[value]` structs
in lean2rr). -/

inductive Tree where
  | node (v : Nat) (cs : Array Tree)

instance : Inhabited Tree := ⟨.node 0 #[]⟩

@[noinline] def Tree.kidAt (t : Tree) (i : Nat) : Nat := match t with
  | .node _ cs => match cs[i]! with
    | .node v _ => v

@[noinline] def Tree.addKid (t : Tree) (k : Tree) : Tree := match t with
  | .node v cs => .node v (cs.push k)

partial def Tree.sum : Tree → Nat
  | .node v cs => cs.foldl (fun acc c => acc + c.sum) v

def Tree.size : Tree → Nat
  | .node _ cs => cs.size

structure J where
  name : String
  kids : Array J

instance : Inhabited J := ⟨⟨"", #[]⟩⟩

@[noinline] def jAt (j : J) (i : Nat) : Nat := (j.kids[i]!).name.length

mutual
  inductive A where
    | mk (bs : Array B)
  inductive B where
    | mk (a : A) (n : Nat)
end

instance : Inhabited B := ⟨.mk (.mk #[]) 0⟩

@[noinline] def B.n' : B → Nat
  | .mk _ n => n

-- B first: its field A is lowered while B's fields are
@[noinline] def firstB (b : B) (i : Nat) : Nat := match b with
  | .mk (.mk bs) _ => (bs[i]!).n'

-- A first
@[noinline] def firstA (a : A) (i : Nat) : Nat := match a with
  | .mk bs => (bs[i]!).n'

mutual
  inductive A2 where
    | mk (b : B2)
  inductive B2 where
    | leaf
    | node (xs : Array A2) (n : Nat)
end

instance : Inhabited A2 := ⟨.mk .leaf⟩

@[noinline] partial def B2.total : B2 → Nat
  | .leaf => 0
  | .node xs n => xs.foldl (fun acc (a : A2) => match a with | .mk b => acc + b.total) n

inductive R where
  | mk (xs : Array R)

instance : Inhabited R := ⟨.mk #[]⟩

@[noinline] def R.width : R → Nat
  | .mk xs => xs.size

@[noinline] def R.at (r : R) (i : Nat) : Nat := match r with
  | .mk xs => (xs[i]!).width

def main (args : List String) : IO Unit := do
  let k := args.length
  let n := 10000 + k
  let t := Tree.node 0 ((Array.range n).map fun i => .node i #[])
  let mut s := 0
  for i in [0:200000] do s := s + t.kidAt (i % n)
  IO.println s!"kidAt {s}"
  let mut u := Tree.node k #[]
  for i in [0:50000] do u := u.addKid (.node i #[])
  IO.println s!"push {u.size} {u.sum} {t.sum}"
  let j : J := ⟨"root", (Array.range n).map fun i => ⟨toString i, #[]⟩⟩
  let mut sj := 0
  for i in [0:200000] do sj := sj + jAt j (i % n)
  IO.println s!"J {sj}"
  let b : B := .mk (.mk ((Array.range n).map fun i => .mk (.mk #[]) i)) 0
  let a : A := .mk ((Array.range n).map fun i => .mk (.mk #[]) (2 * i))
  let mut sb := 0
  for i in [0:200000] do sb := sb + firstB b (i % n) + firstA a (i % n)
  IO.println s!"mutual {sb}"
  let b2 : B2 := .node ((Array.range 100).map fun i => .mk (.node #[.mk (.node #[] i)] 1)) k
  IO.println s!"mutual one-field {b2.total}"
  let r : R := .mk ((Array.range n).map fun i => .mk (Array.replicate (i % 7) (.mk #[])))
  let mut sr := 0
  for i in [0:200000] do sr := sr + r.at (i % n)
  IO.println s!"R {sr}"
