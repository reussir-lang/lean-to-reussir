/-! Runtime test: structural conversions (plan §5.1) of values 300000 levels
deep whose recursion goes through a mediating type: Sum, `Option (Option _)`,
a user-written option, a structure, a pair holding two recursive values, a
structure holding a List, `List (List (List _))`, a mutual partner. Each is
built typed (`Nat` elements), put in an existential package (the uniform
representation), walked there and dropped; one comes back to typed code
(`h ▸`). Run at an 8 MB stack (`RtConvMediated.pipe`): a conversion or free
that took a stack frame per cell would need at least 300000 frames of 32
bytes (reussir-bugs/13). RtConvDeep has the direct shapes.
A coverage test from Crane's test corpus (Bloomberg's Rocq-to-C++ extractor,
whose regression tests document shapes that broke a typed, reference-counted
code generator); the code is new, the shapes are those of Crane's
deep-copy and destructor tests: tests/regression/mutual_value_deep_copy,
list_self_deep_copy, pair_self_deep_copy, optional_self_deep_copy,
sum_drain, double_option_nest, option_deep_drain, user_option_wrapper,
two_level_mediation, triple_list_drain, pair_both_recursive,
record_mediated_drain.
From the round-9 review, area crane (rv9/crane), program CrConv. -/

namespace RtConvMediated

inductive SD (α : Type) | n (s : Sum α (SD α))
def SD.depth {α} : SD α → Nat → Nat
  | .n (.inl _), a => a
  | .n (.inr u), a => u.depth (a + 1)
def SD.leafv {α} (f : α → Nat) : SD α → Nat
  | .n (.inl x) => f x
  | .n (.inr u) => u.leafv f

inductive OO (α : Type) | node (k : α) (c : Option (Option (OO α)))
def OO.spine {α} (f : α → Nat) : OO α → Nat → Nat
  | .node k (some (some c)), a => c.spine f (a + f k % 2)
  | .node k _, a => a + f k

inductive Opt (α : Type) | none | some (a : α)
inductive UW (α : Type) | node (k : α) (c : Opt (UW α))
def UW.spine {α} (f : α → Nat) : UW α → Nat → Nat
  | .node k (.some c), a => c.spine f (a + f k % 2)
  | .node k .none, a => a + f k

structure Cell (β : Type) where
  hd : Nat
  tl : β
inductive RM (α : Type) | stop (x : α) | go (c : Cell (RM α))
def RM.spine {α} (f : α → Nat) : RM α → Nat → Nat
  | .go ⟨_, c⟩, a => c.spine f (a + 1)
  | .stop x, a => a + f x

inductive PB (α : Type) | leaf (k : α) | br (p : PB α × PB α)
def PB.spine {α} (f : α → Nat) : PB α → Nat → Nat
  | .br (x, .leaf k), a => x.spine f (a + f k % 2)
  | .br (x, _), a => x.spine f a
  | .leaf k, a => a + f k

structure W (β : Type) where
  k : Nat
  xs : List β
inductive TL (α : Type) | node (v : α) (w : W (TL α))
def TL.spine {α} (f : α → Nat) : TL α → Nat → Nat
  | .node v ⟨_, c :: _⟩, a => c.spine f (a + f v % 2)
  | .node v _, a => a + f v

inductive TR (α : Type) | node (k : α) (c : List (List (List (TR α))))
def TR.spine {α} (f : α → Nat) : TR α → Nat → Nat
  | .node k [[[c]]], a => c.spine f (a + f k % 2)
  | .node k _, a => a + f k

mutual
inductive MA (α : Type) | stop (x : α) | node (b : Bool) (x : MB α)
inductive MB (α : Type) | node (a : MA α) (v : α)
end
def MA.spine {α} (f : α → Nat) : MA α → Nat → Nat
  | .node _ (.node c v), a => c.spine f (a + f v % 2)
  | .stop x, a => a + f x

@[noinline] def mkSD (n : Nat) : SD Nat := Id.run do
  let mut x := SD.n (.inl 7)
  for _ in [0:n] do x := .n (.inr x)
  return x
@[noinline] def mkOO (n : Nat) : OO Nat := Id.run do
  let mut x := OO.node 3 (some none)
  for i in [0:n] do x := .node i (some (some x))
  return x
@[noinline] def mkUW (n : Nat) : UW Nat := Id.run do
  let mut x := UW.node 3 .none
  for i in [0:n] do x := .node i (.some x)
  return x
@[noinline] def mkRM (n : Nat) : RM Nat := Id.run do
  let mut x := RM.stop 5
  for i in [0:n] do x := .go ⟨i, x⟩
  return x
@[noinline] def mkPB (n : Nat) : PB Nat := Id.run do
  let mut x := PB.leaf 1
  for i in [0:n] do x := .br (x, .leaf i)
  return x
@[noinline] def mkTL (n : Nat) : TL Nat := Id.run do
  let mut x := TL.node 2 ⟨0, []⟩
  for i in [0:n] do x := .node i ⟨i, [x]⟩
  return x
@[noinline] def mkTR (n : Nat) : TR Nat := Id.run do
  let mut x := TR.node 4 []
  for i in [0:n] do x := .node i [[[x]]]
  return x
@[noinline] def mkMA (n : Nat) : MA Nat := Id.run do
  let mut x := MA.stop 6
  for i in [0:n] do x := .node (i % 2 == 0) (.node x i)
  return x

-- existential packages: the payload's type is not static, so the value is held
-- in the uniform representation and walked by the uniform instance
structure Pkg (F : Type → Type) where
  α : Type
  v : F α
  f : α → Nat
@[noinline] def walkSD (p : Pkg SD) : Nat := p.v.depth 0 + p.v.leafv p.f
@[noinline] def walkOO (p : Pkg OO) : Nat := p.v.spine p.f 0
@[noinline] def walkUW (p : Pkg UW) : Nat := p.v.spine p.f 0
@[noinline] def walkRM (p : Pkg RM) : Nat := p.v.spine p.f 0
@[noinline] def walkPB (p : Pkg PB) : Nat := p.v.spine p.f 0
@[noinline] def walkTL (p : Pkg TL) : Nat := p.v.spine p.f 0
@[noinline] def walkTR (p : Pkg TR) : Nat := p.v.spine p.f 0
@[noinline] def walkMA (p : Pkg MA) : Nat := p.v.spine p.f 0

-- the uniform value comes back to typed code
@[noinline] def roundTrip (p : Pkg SD) (h : p.α = Nat) : SD Nat := h ▸ p.v

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 300000
  IO.println s!"sum {walkSD ⟨Nat, mkSD n, id⟩}"
  IO.println s!"option-option {walkOO ⟨Nat, mkOO n, id⟩}"
  IO.println s!"user-option {walkUW ⟨Nat, mkUW n, id⟩}"
  IO.println s!"record {walkRM ⟨Nat, mkRM n, id⟩}"
  IO.println s!"pair-both {walkPB ⟨Nat, mkPB n, id⟩}"
  IO.println s!"wrapper-list {walkTL ⟨Nat, mkTL n, id⟩}"
  IO.println s!"triple-list {walkTR ⟨Nat, mkTR n, id⟩}"
  IO.println s!"mutual {walkMA ⟨Nat, mkMA n, id⟩}"
  let p : Pkg SD := ⟨Nat, mkSD n, id⟩
  IO.println s!"roundTrip {(roundTrip p rfl).depth 0} {walkSD p}"

end RtConvMediated

def main (args : List String) : IO Unit := RtConvMediated.main args
