/-! Runtime test: structural conversions to and from uniform code. A binary
tree (at Nat and UInt8), a rose tree with Array children and u8/u32/String
fields (at Nat and String), mutual inductives, `Array (Option (Tr α × List α))`
and `Array (W α) × List (List α)` (at Nat and Ordering) pass through
polymorphic recursion, whose growing type argument sends them to the uniform
instance (C[T] → C[Box] and back); a 20000-deep left spine is converted too
(an explicit-stack loop, no deep recursion).
From the round-7 review, area R (rv7/repr), check R7Conv. Five of its 14
cases (Float × String tree, UInt8 rose, Float32 mutual, Bool nested, Float W)
are left out to keep the build near a minute; each only repeats a shape above
at another element type. -/

-- Structural conversions (typed <-> uniform `Box` instantiations): trees, rose trees with
-- arrays, mutual inductives, nested containers; both through origin and rebuilt.
inductive Tr (α : Type) where
  | leaf
  | node (l : Tr α) (k : α) (r : Tr α)

def Tr.map {α β : Type} (f : α → β) : Tr α → Tr β
  | .leaf => .leaf
  | .node l k r => .node (l.map f) (f k) (r.map f)

def Tr.toList {α : Type} : Tr α → List α
  | .leaf => []
  | .node l k r => l.toList ++ [k] ++ r.toList

def Tr.size {α : Type} : Tr α → Nat
  | .leaf => 0
  | .node l _ r => l.size + 1 + r.size

inductive Rose (α : Type) where
  | node (tag : UInt8) (v : α) (kids : Array (Rose α)) (w : UInt32) (name : String)

def Rose.map {α β : Type} (f : α → β) : Rose α → Rose β
  | .node t v ks w nm => .node t (f v) (ks.map (fun k => Rose.map f k)) w nm

def Rose.show {α : Type} [ToString α] : Rose α → String
  | .node t v ks w nm => s!"({t} {v} {w} {nm} {ks.map (fun k => Rose.show k)})"

mutual
  inductive A (α : Type) where
    | a (x : α) (bs : List (B α)) (tag : UInt16)
    | stop
  inductive B (α : Type) where
    | b (y : α) (a1 : A α) (a2 : A α)
end

mutual
  def A.map {α β : Type} (f : α → β) : A α → A β
    | .a x bs t => .a (f x) (B.mapL f bs) t
    | .stop => .stop
  def B.mapL {α β : Type} (f : α → β) : List (B α) → List (B β)
    | [] => []
    | .b y a1 a2 :: rest => .b (f y) (a1.map f) (a2.map f) :: B.mapL f rest
end

mutual
  def A.show {α : Type} [ToString α] : A α → String
    | .a x bs t => s!"a({x} {t} {B.showL bs})"
    | .stop => "stop"
  def B.showL {α : Type} [ToString α] : List (B α) → String
    | [] => "."
    | .b y a1 a2 :: rest => s!"b({y} {a1.show} {a2.show}) " ++ B.showL rest
end

structure W (α : Type) where
  v : α

-- Uniform code: the recursive call grows `β`, so it goes to the instance where every type
-- argument is `lcAny`: `x` crosses into `X Box` there.
def goT {α β : Type} (n : Nat) (x : Tr α) (b : β) (f : α → α) (k : Tr α → String) : String :=
  match n with
  | 0 => k (x.map f) ++ " / " ++ k x
  | n+1 => goT n x (b, b) f k

def goR {α β : Type} (n : Nat) (x : Rose α) (b : β) (f : α → α) (k : Rose α → String) : String :=
  match n with
  | 0 => k (x.map f) ++ " / " ++ k x
  | n+1 => goR n x (b, b) f k

def goA {α β : Type} (n : Nat) (x : A α) (b : β) (f : α → α) (k : A α → String) : String :=
  match n with
  | 0 => k (x.map f) ++ " / " ++ k x
  | n+1 => goA n x (b, b) f k

def goN {α β : Type} (n : Nat) (x : Array (Option (Tr α × List α))) (b : β) (f : α → α)
    (k : Array (Option (Tr α × List α)) → String) : String :=
  match n with
  | 0 => k (x.map (·.map fun (t, l) => (t.map f, l.map f))) ++ " / " ++ k x
  | n+1 => goN n x (b, b) f k

def goW {α β : Type} (n : Nat) (x : Array (W α) × List (List α)) (b : β) (f : α → α)
    (k : Array (W α) × List (List α) → String) : String :=
  match n with
  | 0 => k (x.1.map (fun w => ⟨f w.v⟩), x.2.map (·.map f)) ++ " / " ++ k x
  | n+1 => goW n x (b, b) f k

def mkTr (lo hi : Nat) : Tr Nat :=
  if h : lo < hi then
    let m := (lo + hi) / 2
    .node (mkTr lo m) m (mkTr (m + 1) hi)
  else .leaf
termination_by hi - lo

def spine (n : Nat) : Tr Nat := Id.run do
  let mut t := Tr.leaf
  for i in [0:n] do t := .node t i .leaf
  return t

def mkRose (d : Nat) (v : Nat) : Rose Nat :=
  match d with
  | 0 => .node 7 v #[] 70000 "leaf"
  | d+1 => .node (UInt8.ofNat d) v #[mkRose d (v * 2), mkRose d (v * 2 + 1), .node 1 v #[] 3 ""] (UInt32.ofNat (v + 100000)) s!"n{v}"

def main (args : List String) : IO Unit := do
  let z := args.length
  let t := mkTr z (z + 10)
  IO.println (goT 2 t () (· + 1000) fun t => s!"{t.toList}")
  let t8 := (mkTr z (z + 6)).map (fun k => (UInt8.ofNat (k + 250)))
  IO.println (goT 2 t8 () (· + 3) fun t => s!"{t.toList}")
  let ts := spine (20000 + z)
  IO.println (goT 2 ts () (· + 1) fun t => s!"{t.size} {t.toList.take 3}")
  let r := mkRose 3 (1 + z)
  IO.println (goR 2 r () (· * 10) Rose.show)
  let rs := (mkRose 2 (1 + z)).map (fun v => s!"<{v}>")
  IO.println (goR 1 rs () (· ++ "?") Rose.show)
  let am : A Nat := .a 1 [.b 2 (.a 3 [] 4) .stop, .b 5 .stop (.a 6 [.b 7 .stop .stop] 8)] 9
  IO.println (goA 2 am () (· + 100) A.show)
  let nx : Array (Option (Tr Nat × List Nat)) := #[none, some (mkTr 0 3, [1, 2]), some (.leaf, []), none]
  IO.println (goN 2 nx () (· + 7) fun a => s!"{a.toList.map (·.map fun (t, l) => (t.toList, l))}")
  let w : Array (W Nat) × List (List Nat) := (#[⟨1⟩, ⟨2 + z⟩, ⟨2^64⟩], [[1, 2], [], [3]])
  IO.println (goW 2 w () (· + 1) fun (a, l) => s!"{a.toList.map (·.v)} {l}")
  let wo : Array (W Ordering) × List (List Ordering) := (#[⟨.lt⟩, ⟨.gt⟩], [[.eq]])
  IO.println (goW 2 wo () Ordering.swap fun (a, l) => s!"{a.toList.map (fun w => repr w.v)} {l.map (·.map fun o => repr o)}")

