/-! Runtime test: cases of the shared dependent-type corpus (programs built
by another translator's team and checked against native Lean), combined:
each case keeps its code in a namespace named after its case id, and `main`
runs each with that case's arguments in this order, printing `-- <id>`
before it (and `exit <code>` after a `main : IO UInt32`). The cases, with
what each checks:
- `A1007`: A recursive type laid out by T5 case (a) (`node : T α → T α → T α
  | leaf : α → T α`, no nullary constructor) under a conversion: its values
  hold pointers to their children and ...
- `A1011`: A rose tree (`node (v : α) (cs : List (Rose α))`) whose subtrees
  are shared three times per level (3^40 paths), converted through the memo,
  which keys its children's list cells.
- `A1012`: An `Array` below a list cell under a conversion (`List (Array ι)`
  at a rank-2 handler's two types): one value can reach it twice and Lower
  passes a borrowed array as a slice, so no key ...
- `A1013`: A shared tree `t_k := node t_{k-1} v t_{k-1}` (k + 1 distinct
  nodes, 2^k paths) converted at a rank-2 handler's two types through the
  conversion memo: each distinct node rebuilt once, so k ...
- `A1015`: A closed term Lean's compiler shares between two instantiations
  of an erased type argument, passed through a wrapper (`ap2 f x := ap f x`,
  `ap2 List.length ["a", "b"] + ap2 List.length ...
- `A1016`: One shared closed term `List.length` read at three types (`List
  String`, `List Nat`, `List Bool`): the marks hold every instantiation's
  binder
- `A1017`: Shared trees whose nodes hold a by-value field (a pair, a
  structure, an option) converted through the conversion memo: the key is
  read from the source before ...
- `A1018`: Lists of pairs and of a structure whose tails are shared across
  lists, converted through the memo's two list loops: the walk holds each
  cell before matching ...
- `A1019`: Polymorphic recursion, `grow {α} : Nat → α → List α`
  (validate/reject's `depNested`, the types-names cases `dep-nested` and
  `reject-polyrec`), its site-keyed `List` read at `List Nat` and at a pair
  and a ...
- `A1020`: One shared closed term `List.length` read by two callees at `List
  String` and `List Nat`, the second through a list literal of two cells
  (`total List.length [nums, nums]`
- `A1021`: A shared closed term `List.reverse` read at `List String` and
  `List Nat`, whose result varies with its argument: the shared-value marks
  meet a ... -/

namespace A1007

inductive T (α : Type) where
  | node : T α → T α → T α
  | leaf : α → T α

def grow {α : Type} (a : α) : Nat → T α
  | 0 => .leaf a
  | k + 1 => let t := grow a k; .node t t

@[noinline] def both (h : {ι : Type} → [ToString ι] → T ι → String) (a : T Nat) (b : T String) : String :=
  h a ++ "|" ++ h b

def leftmost {ι : Type} [ToString ι] : T ι → String
  | .leaf v => toString v
  | .node l _ => leftmost l

def caseMain (args : List String) : IO Unit := do
  let k := (args.head? >>= String.toNat?).getD 20
  IO.println (both (fun t => leftmost t) (grow 7 k) (grow "s" k))
end A1007

namespace A1011

inductive Rose (α : Type) where
  | node (v : α) (cs : List (Rose α))

def shared {α : Type} (f : Nat → α) : Nat → Rose α
  | 0 => .node (f 0) []
  | k + 1 => let t := shared f k; .node (f (k + 1)) [t, t, t]

@[noinline] def both (h : {ι : Type} → [ToString ι] → Rose ι → String) (a : Rose Nat) (b : Rose String) : String :=
  h a ++ "|" ++ h b

def top {ι : Type} [ToString ι] : Rose ι → String
  | .node v cs => s!"{v}/{cs.length}"

def caseMain (args : List String) : IO Unit := do
  let k := (args.head? >>= String.toNat?).getD 40
  IO.println (both (fun t => top t) (shared id k) (shared (fun i => s!"s{i}") k))
end A1011

namespace A1012

@[noinline] def lens (h : {ι : Type} → List (Array ι) → Nat) (a : List (Array Nat)) (b : List (Array String)) : Nat :=
  h a + h b

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 10
  IO.println (lens (fun l => l.length + (l.headD #[]).size) [Array.range n] [#["a"]])
end A1012

namespace A1013

inductive Tree (α : Type) where
  | leaf
  | node (l : Tree α) (v : α) (r : Tree α)

def doubling {α : Type} (f : Nat → α) : Nat → Tree α
  | 0 => .leaf
  | k + 1 => let t := doubling f k; .node t (f k) t

@[noinline] def both (h : {ι : Type} → [ToString ι] → Tree ι → String) (a : Tree Nat) (b : Tree String) : String :=
  h a ++ "|" ++ h b

def rootOf {ι : Type} [ToString ι] : Tree ι → String
  | .leaf => "leaf"
  | .node _ v _ => toString v

def caseMain (args : List String) : IO Unit := do
  let k := (args.head? >>= String.toNat?).getD 60
  IO.println (both (fun t => rootOf t) (doubling id k) (doubling (fun i => s!"s{i}") k))
end A1013

namespace A1015

@[noinline] def ap {α β : Type} (f : α → β) (x : α) : β := f x
@[noinline] def ap2 {α β : Type} (f : α → β) (x : α) : β := ap f x
def caseMain (args : List String) : IO Unit := do
  let k := args.length
  IO.println s!"{ap2 List.length ["a", "b"] + ap2 List.length [k]}"
end A1015

namespace A1016

@[noinline] def ap {α β : Type} (f : α → β) (x : α) : β := f x
def caseMain (args : List String) : IO Unit := do
  let k := args.length
  IO.println s!"{ap List.length ["a", "b"] + ap List.length [k, k, k] + ap List.length [k == 0]}"
end A1016

namespace A1017

structure V (α : Type) where
  id : Nat
  label : α

inductive PT (α : Type) where
  | leaf
  | node (l : PT α) (p : Nat × α) (r : PT α)

inductive VT (α : Type) where
  | leaf
  | node (l : VT α) (v : V α) (r : VT α)

inductive OT (α : Type) where
  | leaf
  | node (l : OT α) (o : Option α) (r : OT α)

def dblP {α : Type} (f : Nat → α) : Nat → PT α
  | 0 => .leaf
  | k + 1 => let t := dblP f k; .node t (k, f k) t

def dblV {α : Type} (f : Nat → α) : Nat → VT α
  | 0 => .leaf
  | k + 1 => let t := dblV f k; .node t { id := k, label := f k } t

def dblO {α : Type} (f : Nat → α) : Nat → OT α
  | 0 => .leaf
  | k + 1 => let t := dblO f k; .node t (if k % 2 == 0 then some (f k) else none) t

@[noinline] def bothP (h : {ι : Type} → [ToString ι] → PT ι → String) (a : PT Nat) (b : PT String) : String := h a ++ "|" ++ h b
@[noinline] def bothV (h : {ι : Type} → [ToString ι] → VT ι → String) (a : VT Nat) (b : VT String) : String := h a ++ "|" ++ h b
@[noinline] def bothO (h : {ι : Type} → [ToString ι] → OT ι → String) (a : OT Nat) (b : OT String) : String := h a ++ "|" ++ h b

def rootP {ι : Type} [ToString ι] : PT ι → String
  | .leaf => "leaf"
  | .node _ (n, v) _ => s!"{n}:{v}"
def rootV {ι : Type} [ToString ι] : VT ι → String
  | .leaf => "leaf"
  | .node _ v _ => s!"{v.id}:{v.label}"
def rootO {ι : Type} [ToString ι] : OT ι → String
  | .leaf => "leaf"
  | .node _ o _ => s!"{o}"

def caseMain (args : List String) : IO Unit := do
  let k := (args[0]? >>= String.toNat?).getD 20
  let which := (args[1]? >>= String.toNat?).getD 0
  if which == 0 || which == 1 then IO.println (bothP (fun t => rootP t) (dblP id k) (dblP toString k))
  if which == 0 || which == 2 then IO.println (bothV (fun t => rootV t) (dblV id k) (dblV toString k))
  if which == 0 || which == 3 then IO.println (bothO (fun t => rootO t) (dblO id k) (dblO toString k))
end A1017

namespace A1018

structure V (α : Type) where
  id : Nat
  label : α

@[noinline] def lensP (h : {ι : Type} → List (List (Nat × ι)) → Nat) (a : List (List (Nat × Nat))) (b : List (List (Nat × String))) : Nat :=
  h a + h b

@[noinline] def lensV (h : {ι : Type} → Array (List (V ι)) → Nat) (a : Array (List (V Nat))) (b : Array (List (V String))) : Nat :=
  h a + h b

/-- `[l_n, …, l_1]` with `l_i = x_i :: l_{i-1}`: the lists share their tails. -/
def tails {β : Type} (g : Nat → β) (n : Nat) : List (List β) := Id.run do
  let mut l : List β := []
  let mut out : List (List β) := []
  for i in [0:n] do
    l := g i :: l
    out := l :: out
  return out

def caseMain (args : List String) : IO Unit := do
  let n := (args[0]? >>= String.toNat?).getD 1000
  let which := (args[1]? >>= String.toNat?).getD 0
  if which == 0 || which == 1 then
    IO.println (lensP (fun l => l.length + (l.headD []).length) (tails (fun i => (i, i)) n) (tails (fun i => (i, toString i)) n))
  if which == 0 || which == 2 then
    IO.println (lensV (fun a => a.size + (a[0]?.map List.length).getD 0) (tails (fun i => ({ id := i, label := i } : V Nat)) n).toArray (tails (fun i => ({ id := i, label := toString i } : V String)) n).toArray)
end A1018

namespace A1019


def grow {α : Type} : Nat → α → List α
  | 0, x => [x]
  | n + 1, x => (grow n (x, x)).map Prod.fst

def readGrow (n : Nat) : Nat := (grow n (5 : Nat)).foldl (· + ·) 0

def caseMain (args : List String) : IO Unit := do
  for a in args do
    let n := a.toNat!
    IO.println s!"{readGrow n}"
    IO.println s!"{grow n ("s" ++ a)}"
    IO.println s!"{grow n ((n, a) : Nat × String)}"
    IO.println s!"{(grow n [n, n + 1]).length}"
end A1019

namespace A1020

@[noinline] def sizeBy {α : Type} (f : α → Nat) (x : α) : Nat := f x
@[noinline] def total {α : Type} (f : α → Nat) (xs : List α) : Nat := xs.foldl (fun acc x => acc + f x) 0
def caseMain (args : List String) : IO Unit := do
  let words := args ++ ["alpha"]
  let nums := List.range (args.length + 3)
  IO.println s!"{sizeBy List.length words} {total List.length [nums, nums]}"
end A1020

namespace A1021

@[noinline] def ap {α β : Type} (f : α → β) (x : α) : β := f x
@[noinline] def ap2 {α β : Type} (f : α → β) (x : α) : β := ap f x
@[noinline] def ap3 {α β : Type} (f : α → β) (x : α) : β := ap2 f x
@[noinline] def rec (k : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => ap List.length ["a", "b"] + ap List.length [k, n] + rec k n
def caseMain (args : List String) : IO Unit := do
  let k := args.length
  IO.println s!"{ap List.reverse ["p", "q"]} {ap List.reverse [k, k + 1]}"
end A1021

def main : IO Unit := do
  IO.println "-- A1007"
  A1007.caseMain ["5"]
  IO.println "-- A1011"
  A1011.caseMain ["3"]
  IO.println "-- A1012"
  A1012.caseMain ["3"]
  IO.println "-- A1013"
  A1013.caseMain ["5"]
  IO.println "-- A1015"
  A1015.caseMain ["x", "y"]
  IO.println "-- A1016"
  A1016.caseMain ["x", "y"]
  IO.println "-- A1017"
  A1017.caseMain ["5", "2"]
  IO.println "-- A1018"
  A1018.caseMain ["5", "2"]
  IO.println "-- A1019"
  A1019.caseMain ["7", "12"]
  IO.println "-- A1020"
  A1020.caseMain ["x", "y"]
  IO.println "-- A1021"
  A1021.caseMain ["x", "y"]
