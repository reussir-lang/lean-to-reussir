/-! Runtime test: shared values of every shape stay shared when they go
through code that does not know their element type (blowup audit BA-02,
the rose tree, and BA-07, the suffixes of a list; branch fix-conv-sharing's
RtConvShareShapes without its address checks). Each value below reaches
one object through several paths, exponentially many for the recursive
ones, and is packed in an existential (its element type a field) and read
there along one path:
- a diamond through an array (a node's array holds one child three times);
- mutual inductives (two references to one object of the other type);
- a nested inductive (a rose tree's `List` of children holds one child
  twice);
- one array reached twice (both array fields of a node are one array,
  an empty one at the bottom; both fields of a non-recursive structure
  are one array);
- the suffixes of a list, which share their tails (`List (List α)`);
- function values and thunks inside a shared tree.
Native Lean holds O(n) objects for each and does O(n) work. A translation
that rebuilds a value when it changes its representation builds every
path (3^n, 2^n, or n^2 for the suffixes). The output is checked here; the
allocations and the peak memory at n = 10 and n = 16 by
tests/runtime/alloc-check.sh (RtDepShareShapes.alloc). Argument: N
(default 12). -/

-- A diamond through an array.
inductive ATree (α : Type) where
  | leaf (x : α)
  | node (cs : Array (ATree α))

@[noinline] def abuild : Nat → ATree Nat
  | 0 => .leaf 3
  | n + 1 => let t := abuild n; .node #[t, t, t]

structure PA where
  α : Type
  t : ATree α
  f : α → Nat

@[noinline] partial def aCheck (p : PA) : Nat × Nat := go p.t 0
where
  go : ATree p.α → Nat → Nat × Nat
    | .leaf x, d => (d, p.f x)
    | .node cs, d =>
      match cs[2]? with
      | some c => go c (d + cs.size)
      | none => (d, 0)

-- Mutual inductives.
mutual
inductive MA (α : Type) where
  | leaf (x : α)
  | two (l r : MB α)
inductive MB (α : Type) where
  | wrap (a : MA α) (tag : Nat)
end

@[noinline] def mbuild : Nat → MA Nat
  | 0 => .leaf 1
  | n + 1 => let b := MB.wrap (mbuild n) n; .two b b

structure PM where
  α : Type
  t : MA α

@[noinline] def mCheck (p : PM) : Nat := go p.t 0
where
  go {α : Type} : MA α → Nat → Nat
    | .leaf _, d => d
    | .two _ r, d =>
      match r with
      | .wrap a tag => go a (d + tag)

-- A nested inductive.
inductive Rose (α : Type) where
  | node (x : α) (kids : List (Rose α))

@[noinline] def rbuild : Nat → Rose Nat
  | 0 => .node 5 []
  | n + 1 => let t := rbuild n; .node n [t, t]

structure PR where
  α : Type
  t : Rose α
  f : α → Nat

@[noinline] def rCheck (p : PR) : Nat × Nat := go p.t 0 0
where
  go : Rose p.α → Nat → Nat → Nat × Nat
    | .node x [_, b], d, s => go b (d + 1) (s + p.f x)
    | .node x _, d, s => (d, s + p.f x)

-- One array reached twice.
inductive STree (α : Type) where
  | leaf (x : α)
  | node (a b : Array (STree α))

@[noinline] def sbuild : Nat → STree Nat
  | 0 => let arr : Array (STree Nat) := #[]; .node arr arr
  | n + 1 => let arr := #[sbuild n]; .node arr arr

structure PS where
  α : Type
  t : STree α

@[noinline] partial def sCheck (p : PS) : Nat := go p.t 0
where
  go {α : Type} : STree α → Nat → Nat
    | .leaf _, d => d
    | .node a b, d =>
      match b[0]? with
      | some c => go c (d + a.size)
      | none => d

structure Two (α : Type) where
  a : Array α
  b : Array α

structure PT where
  α : Type
  t : Two α
  f : α → Nat

@[noinline] def mkTwo (n : Nat) : Two Nat := let arr := (List.range n).toArray; ⟨arr, arr⟩

@[noinline] def tCheck (p : PT) : Nat × Nat :=
  (p.t.a.size + p.t.b.size, p.t.a.foldl (fun s x => s + p.f x) 0 + (p.t.b.back?.map p.f).getD 0)

-- The suffixes of a list (each suffix is the tail of the one before).
@[noinline] def suffixes (n : Nat) : List (List Nat) := go (List.range n) []
where
  go : List Nat → List (List Nat) → List (List Nat)
    | [], acc => acc.reverse
    | l@(_ :: t), acc => go t (l :: acc)

structure PL where
  α : Type
  l : List (List α)
  f : α → Nat

@[noinline] def lCheck (p : PL) : Nat × Nat :=
  p.l.foldl (fun (k, s) xs => match xs with
    | [] => (k + 1, s)
    | x :: _ => (k + 1, s + p.f x)) (0, 0)

-- Function values and thunks inside a shared tree.
inductive Tree' (α : Type) where
  | leaf (x : α)
  | node (l r : Tree' α)

@[noinline] def fbuild : Nat → Tree' (Nat → Nat)
  | 0 => .leaf (· + 11)
  | n + 1 => let t := fbuild n; .node t t

structure PF where
  α : Type
  t : Tree' α
  ap : α → Nat → Nat

@[noinline] def fCheck (p : PF) (x : Nat) : Nat := go p.t 0
where
  go : Tree' p.α → Nat → Nat
    | .leaf f, d => d + p.ap f x
    | .node l _, d => go l (d + 1)

inductive TT (α : Type) where
  | leaf (x : α)
  | node (l r : Thunk (TT α))

@[noinline] def tbuild : Nat → TT Nat
  | 0 => .leaf 2
  | n + 1 => let th := Thunk.pure (tbuild n); .node th th

structure PTT where
  α : Type
  t : TT α
  f : α → Nat

@[noinline] def ttCheck (p : PTT) : Nat × Nat := go p.t 0
where
  go : TT p.α → Nat → Nat × Nat
    | .leaf x, d => (d, p.f x)
    | .node _ r, d => go r.get (d + 1)

def main (args : List String) : IO Unit := do
  let n := (args.headD "12").toNat!
  IO.println s!"array diamond {aCheck ⟨Nat, abuild (n * 3 / 4), id⟩}"
  IO.println s!"mutual {mCheck ⟨Nat, mbuild n⟩}"
  IO.println s!"nested {rCheck ⟨Nat, rbuild n, id⟩}"
  IO.println s!"array twice {sCheck ⟨Nat, sbuild n⟩}"
  IO.println s!"structure with one array twice {tCheck ⟨Nat, mkTwo 10000, id⟩}"
  IO.println s!"suffixes {lCheck ⟨Nat, suffixes (n * 100), id⟩}"
  IO.println s!"function values {fCheck ⟨Nat → Nat, fbuild n, fun f x => f x⟩ 4}"
  IO.println s!"thunks {ttCheck ⟨Nat, tbuild n, id⟩}"
