/-! Runtime test: dropping values 300000 levels deep whose recursion goes
through a mediating type: Sum, a pair holding two recursive values, a
structure holding a List, `List (List (List _))`, a list of pairs, a list of
options, `Option (Option _)`, a user-written option, a structure, an
alternating mutual pair, a user list, a mutual pair through List, and
one-field structures that recurse through Option, List, a pair and a mutual
partner (three of them value structs). Each is built by a loop, walked by a
loop while still held (so the walk frees nothing), and dropped by the call
that takes its last reference (`top`), in one free. Then frees that must stop at a shared cell: a
list whose 300000-cell suffix another live list shares, and a rose tree whose
children list three roots share. Run at an 8 MB stack (`RtDropMediated.pipe`):
a free that took one 32-byte frame per cell (reussir-bugs/13) would need at
least 9.6 MB. RtDropGlue and RtDropDeep have the direct shapes.
A coverage test from Crane's test corpus (Bloomberg's Rocq-to-C++ extractor,
whose regression tests document shapes that broke a typed, reference-counted
code generator); the code is new, the shapes are those of Crane's
tests/regression/sum_drain, pair_both_recursive, two_level_mediation,
triple_list_drain, list_of_list_drain, list_of_prod_deep, assoc_pair_list,
list_option_drain, double_option_nest, option_deep_drain, user_option_wrapper,
record_mediated_drain, singleton_record, mutual_value_deep_destruct,
wrapper_nested_recursion_no_drain, nested_inductive_no_drain,
mutual_list_cycle, rose_shared_suffix_drain, rose_shared_suffix_drain_size.
From the round-9 review, area crane (rv9/crane), programs CrDrain and CrInd. -/

namespace RtDropMediated

inductive SD | n (s : Sum Nat SD)
def SD.depth : SD → Nat → Nat
  | .n (.inl _), a => a
  | .n (.inr u), a => u.depth (a + 1)

inductive PB | leaf (k : Nat) | br (p : PB × PB)
def PB.spine : PB → Nat → Nat
  | .br (x, _), a => x.spine (a + 1)
  | .leaf _, a => a

structure W (α : Type) where
  k : Nat
  xs : List α
inductive TL | node (w : W TL)
def TL.spine : TL → Nat → Nat
  | .node ⟨_, c :: _⟩, a => c.spine (a + 1)
  | _, a => a

inductive TR | node (k : Nat) (c : List (List (List TR)))
def TR.spine : TR → Nat → Nat
  | .node _ [[[c]]], a => c.spine (a + 1)
  | _, a => a

inductive AP | node (k : Nat) (c : List (Nat × AP))
def AP.spine : AP → Nat → Nat
  | .node _ ((_, c) :: _), a => c.spine (a + 1)
  | _, a => a

inductive LO | node (c : List (Option LO))
def LO.spine : LO → Nat → Nat
  | .node (some c :: _), a => c.spine (a + 1)
  | _, a => a

inductive OO | node (k : Nat) (c : Option (Option OO))
def OO.spine : OO → Nat → Nat
  | .node _ (some (some c)), a => c.spine (a + 1)
  | _, a => a

inductive Opt (α : Type) | none | some (a : α)
inductive UW | node (k : Nat) (c : Opt UW)
def UW.spine : UW → Nat → Nat
  | .node _ (.some c), a => c.spine (a + 1)
  | _, a => a

structure Cell (α : Type) where
  hd : Nat
  tl : α
inductive RM | stop | go (c : Cell RM)
def RM.spine : RM → Nat → Nat
  | .go ⟨_, c⟩, a => c.spine (a + 1)
  | .stop, a => a

mutual
inductive MA | stop | node (b : Bool) (x : MB)
inductive MB | node (a : MA)
end
def MA.spine : MA → Nat → Nat
  | .node _ (.node c), a => c.spine (a + 1)
  | .stop, a => a

inductive MyL (α : Type) | nil | cons (a : α) (t : MyL α)
inductive NT | node (k : Nat) (c : MyL NT)
def NT.spine : NT → Nat → Nat
  | .node _ (.cons c _), a => c.spine (a + 1)
  | _, a => a

mutual
inductive Tree | node (k : Nat) (bs : List Branch)
inductive Branch | br (label : String) (t : Tree)
end
def Tree.spine : Tree → Nat → Nat
  | .node _ (.br _ c :: _), a => c.spine (a + 1)
  | _, a => a

inductive Rose | node (v : Nat) (cs : List Rose)
def Rose.spine : Rose → Nat → Nat
  | .node v (c :: _), a => c.spine (a + v)
  | .node v [], a => a + v

@[noinline] def mkSD (n : Nat) : SD := Id.run do
  let mut x := SD.n (.inl 0)
  for _ in [0:n] do x := .n (.inr x)
  return x
@[noinline] def mkPB (n : Nat) : PB := Id.run do
  let mut x := PB.leaf 1
  for i in [0:n] do x := .br (x, .leaf i)
  return x
@[noinline] def mkTL (n : Nat) : TL := Id.run do
  let mut x := TL.node ⟨0, []⟩
  for i in [0:n] do x := .node ⟨i, [x]⟩
  return x
@[noinline] def mkTR (n : Nat) : TR := Id.run do
  let mut x := TR.node 0 []
  for i in [0:n] do x := .node i [[[x]]]
  return x
@[noinline] def mkAP (n : Nat) : AP := Id.run do
  let mut x := AP.node 0 []
  for i in [0:n] do x := .node i [(i, x), (i + 1, .node 0 [])]
  return x
@[noinline] def mkLO (n : Nat) : LO := Id.run do
  let mut x := LO.node []
  for _ in [0:n] do x := .node [some x, none]
  return x
@[noinline] def mkOO (n : Nat) : OO := Id.run do
  let mut x := OO.node 0 (some none)
  for i in [0:n] do x := .node i (some (some x))
  return x
@[noinline] def mkUW (n : Nat) : UW := Id.run do
  let mut x := UW.node 0 .none
  for i in [0:n] do x := .node i (.some x)
  return x
@[noinline] def mkRM (n : Nat) : RM := Id.run do
  let mut x := RM.stop
  for i in [0:n] do x := .go ⟨i, x⟩
  return x
@[noinline] def mkMA (n : Nat) : MA := Id.run do
  let mut x := MA.stop
  for i in [0:n] do x := .node (i % 2 == 0) (.node x)
  return x
@[noinline] def mkNT (n : Nat) : NT := Id.run do
  let mut x := NT.node 0 .nil
  for i in [0:n] do x := .node i (.cons x (.cons (.node 0 .nil) .nil))
  return x
@[noinline] def mkTree (n : Nat) : Tree := Id.run do
  let mut x := Tree.node 0 []
  for i in [0:n] do x := .node i [.br "a" x, .br "b" (.node 1 [])]
  return x
@[noinline] def mkRose (n : Nat) : Rose := Id.run do
  let mut x := Rose.node 1 []
  for _ in [0:n] do x := .node 1 [x]
  return x

-- one-field structures that recurse through Option, List, a pair and a mutual
-- partner
structure Chain where next : Option Chain
structure RoseW where kids : List RoseW
structure PairRec where p : Option (PairRec × Nat)
mutual
structure WA where b : Option WB
structure WB where a : List WA
end
def Chain.len : Chain → Nat → Nat | ⟨none⟩, a => a | ⟨some c⟩, a => c.len (a + 1)
def RoseW.spine : RoseW → Nat → Nat | ⟨c :: _⟩, a => c.spine (a + 1) | ⟨[]⟩, a => a
def PairRec.spine : PairRec → Nat → Nat | ⟨some (q, _)⟩, a => q.spine (a + 1) | ⟨none⟩, a => a
def WA.spine : WA → Nat → Nat | ⟨some ⟨c :: _⟩⟩, a => c.spine (a + 1) | _, a => a
@[noinline] def mkChain (n : Nat) : Chain := Id.run do
  let mut c : Chain := ⟨none⟩
  for _ in [0:n] do c := ⟨some c⟩
  return c
@[noinline] def mkRoseW (n : Nat) : RoseW := Id.run do
  let mut c : RoseW := ⟨[]⟩
  for _ in [0:n] do c := ⟨[c, ⟨[]⟩]⟩
  return c
@[noinline] def mkPairRec (n : Nat) : PairRec := Id.run do
  let mut c : PairRec := ⟨none⟩
  for i in [0:n] do c := ⟨some (c, i)⟩
  return c
@[noinline] def mkWA (n : Nat) : WA := Id.run do
  let mut c : WA := ⟨none⟩
  for _ in [0:n] do c := ⟨some ⟨[c]⟩⟩
  return c

-- A list whose long suffix is shared with another live list: dropping the first
-- must stop at the shared cell.
@[noinline] def mkList (lo n : Nat) (tail : List Nat) : List Nat := Id.run do
  let mut x := tail
  for i in [0:n] do x := (lo + i) :: x
  return x
@[noinline] def sumList (l : List Nat) : Nat := l.foldl (· + ·) 0
@[noinline] def dropAndCount (r : Rose) : Nat := match r with | .node v cs => v + cs.length

-- Shallow use that takes the last reference: the whole value below the top
-- cell is dropped here, in one free.
@[noinline] def top {α} (x : α) (f : α → Nat) : Nat := f x

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 300000
  let x := mkSD n
  IO.println s!"sum-mediated {x.depth 0} {top x fun | .n (.inl _) => 0 | _ => 1}"
  let x := mkPB n
  IO.println s!"pair-both {x.spine 0} {top x fun | .br _ => 1 | _ => 0}"
  let x := mkTL n
  IO.println s!"wrapper-then-list {x.spine 0} {top x fun | .node w => w.k}"
  let x := mkTR n
  IO.println s!"triple-list {x.spine 0} {top x fun | .node k _ => k}"
  let x := mkAP n
  IO.println s!"list-of-prod {x.spine 0} {top x fun | .node k _ => k}"
  let x := mkLO n
  IO.println s!"list-of-option {x.spine 0} {top x fun | .node c => c.length}"
  let x := mkOO n
  IO.println s!"option-option {x.spine 0} {top x fun | .node k _ => k}"
  let x := mkUW n
  IO.println s!"user-option {x.spine 0} {top x fun | .node k _ => k}"
  let x := mkRM n
  IO.println s!"record-mediated {x.spine 0} {top x fun | .go c => c.hd | .stop => 0}"
  let x := mkMA n
  IO.println s!"mutual-alternating {x.spine 0} {top x fun | .node b _ => if b then 1 else 2 | .stop => 0}"
  let x := mkNT n
  IO.println s!"user-list {x.spine 0} {top x fun | .node k _ => k}"
  let x := mkTree n
  IO.println s!"mutual-through-list {x.spine 0} {top x fun | .node k _ => k}"
  let x := mkChain n
  IO.println s!"one-field-option {x.len 0} {top x fun | ⟨none⟩ => 0 | _ => 1}"
  let x := mkRoseW n
  IO.println s!"one-field-list {x.spine 0} {top x (·.kids.length)}"
  let x := mkPairRec n
  IO.println s!"one-field-pair {x.spine 0} {top x fun | ⟨some (_, i)⟩ => i | _ => 0}"
  let x := mkWA n
  IO.println s!"one-field-mutual {x.spine 0} {top x fun | ⟨some _⟩ => 1 | _ => 0}"
  -- shared suffixes
  let suffix := mkList 0 n []
  let a := mkList 1000 n suffix
  let b := mkList 2000 3 suffix
  IO.println s!"shared-suffix-a {sumList a} {top a List.length}"
  IO.println s!"shared-suffix-b {sumList b}"
  let deep := mkRose n
  let kids := [deep, .node 5 []]
  let c1 := dropAndCount (.node 1 kids)
  let c2 := dropAndCount (.node 2 kids)
  let c3 := dropAndCount (.node 3 (.node 7 [] :: kids))
  IO.println s!"rose-shared {c1} {c2} {c3} {(Rose.node 4 kids).spine 0}"

end RtDropMediated

def main (args : List String) : IO Unit := RtDropMediated.main args
