/-
lean2rr classic corpus: `typeclass-generic` (written for this corpus).

A generic `sum [Add α] [OfNat α 0]` and a user-defined class hierarchy
(`Semigroup'` / `Monoid'` with `extends`) with generic functions (`mconcat`,
binary `mpow`), used at `Nat`, `Int`, `UInt64`, `Float`, `String` and user
types (a 2-D vector, 2x2 matrices). Also: instances built from other
instances (products, `Option`, lists), a class with a default method,
existentially packed values carrying their own instance (dynamic
dictionaries), an `outParam` class, and a `Functor` instance for a user type
used through a function generic in the functor.

Size argument n (default 10000000): how many numbers `sum` adds up (in lists
of 10000 elements); the `mpow` and packed-shape loops run n/10 times.
-/

/-! ## A generic sum -/

def sum {α : Type} [Add α] [OfNat α 0] (xs : List α) : α :=
  xs.foldl (· + ·) 0

structure V2 where
  x : Int
  y : Int
deriving BEq, Repr

instance : Add V2 := ⟨fun a b => ⟨a.x + b.x, a.y + b.y⟩⟩
instance : OfNat V2 0 := ⟨⟨0, 0⟩⟩
instance : ToString V2 := ⟨fun v => s!"({v.x}, {v.y})"⟩

/-! ## A user class hierarchy with generic functions -/

class Semigroup' (α : Type) where
  op : α → α → α

class Monoid' (α : Type) extends Semigroup' α where
  unit : α

def mconcat {α : Type} [Monoid' α] (xs : List α) : α :=
  xs.foldl Semigroup'.op Monoid'.unit

/-- Binary exponentiation in any monoid. -/
def mpow {α : Type} [Monoid' α] (x : α) (n : Nat) : α := Id.run do
  let mut result := Monoid'.unit
  let mut base := x
  let mut e := n
  while e > 0 do
    if e % 2 == 1 then result := Semigroup'.op result base
    base := Semigroup'.op base base
    e := e / 2
  return result

instance : Monoid' Nat := { op := (· * ·), unit := 1 }
instance : Monoid' Int := { op := (· + ·), unit := 0 }
instance : Monoid' UInt64 := { op := (· * ·), unit := 1 }
instance : Monoid' Float := { op := (· * ·), unit := 1.0 }
instance : Monoid' String := { op := (· ++ ·), unit := "" }
instance {α : Type} : Monoid' (List α) := { op := (· ++ ·), unit := [] }

/-- Pairs: component-wise, from the components' instances. -/
instance {α β : Type} [Monoid' α] [Monoid' β] : Monoid' (α × β) :=
  { op := fun a b => (Semigroup'.op a.1 b.1, Semigroup'.op a.2 b.2), unit := (Monoid'.unit, Monoid'.unit) }

/-- `Option α` is a monoid for any semigroup `α` (`none` is the unit). -/
instance {α : Type} [Semigroup' α] : Monoid' (Option α) where
  op
    | some a, some b => some (Semigroup'.op a b)
    | some a, none => some a
    | none, b => b
  unit := none

/-- 2x2 matrices over any type with `+`, `*`, `0`, `1`. -/
structure Mat2 (α : Type) where
  a : α
  b : α
  c : α
  d : α

instance {α : Type} [Add α] [Mul α] [OfNat α 0] [OfNat α 1] : Monoid' (Mat2 α) where
  op m n := ⟨m.a * n.a + m.b * n.c, m.a * n.b + m.b * n.d, m.c * n.a + m.d * n.c, m.c * n.b + m.d * n.d⟩
  unit := ⟨1, 0, 0, 1⟩

/-- F(k) as the top-right entry of [[1,1],[1,0]]^k. -/
def fibMat {α : Type} [Add α] [Mul α] [OfNat α 0] [OfNat α 1] (k : Nat) : α :=
  (mpow (⟨1, 1, 1, 0⟩ : Mat2 α) k).b

/-! ## A class with a default method, and dynamic dictionaries -/

class Shape (α : Type) where
  name : α → String
  area : α → Float
  perimeter : α → Float
  describe : α → String := fun s => s!"{name s} area={area s}"

structure Circle where r : Float
structure Rect where
  w : Float
  h : Float

structure Poly where
  sides : Nat
  len : Float

instance : Shape Circle where
  name _ := "circle"
  area c := 3.0 * c.r * c.r
  perimeter c := 6.0 * c.r

instance : Shape Rect where
  name _ := "rect"
  area r := r.w * r.h
  perimeter r := 2.0 * (r.w + r.h)
  describe r := s!"rect {r.w}x{r.h}"

instance : Shape Poly where
  name p := s!"{p.sides}-gon"
  area p := p.sides.toFloat * p.len * p.len / 4.0
  perimeter p := p.sides.toFloat * p.len

/-- A value packed together with its `Shape` instance. -/
structure AnyShape where
  {α : Type}
  [inst : Shape α]
  val : α

instance : Inhabited AnyShape := ⟨⟨Circle.mk 0.0⟩⟩

def AnyShape.area (s : AnyShape) : Float := s.inst.area s.val
def AnyShape.describe (s : AnyShape) : String := s.inst.describe s.val

def totalPerimeter {α : Type} [Shape α] (xs : List α) : Float :=
  xs.foldl (fun acc s => acc + Shape.perimeter s) 0.0

/-! ## An `outParam` class -/

class Container (c : Type) (e : outParam Type) where
  elems : c → List e

structure Bag where
  items : Array Nat

instance : Container Bag Nat := ⟨fun b => b.items.toList⟩
instance {α : Type} : Container (Array α) α := ⟨Array.toList⟩

def containerSum {c e : Type} [Container c e] [Add e] [OfNat e 0] (x : c) : e :=
  sum (Container.elems x)

/-! ## Functor over a user type, used generically -/

inductive Tree (α : Type) where
  | leaf
  | node (l : Tree α) (v : α) (r : Tree α)

def Tree.map {α β : Type} (f : α → β) : Tree α → Tree β
  | .leaf => .leaf
  | .node l v r => .node (l.map f) (f v) (r.map f)

instance : Functor Tree := ⟨Tree.map, fun b t => Tree.map (fun _ => b) t⟩

def Tree.toList {α : Type} : Tree α → List α
  | .leaf => []
  | .node l v r => l.toList ++ [v] ++ r.toList

def Tree.build (lo hi : Nat) : Tree Nat :=
  if h : lo < hi then
    let mid := (lo + hi) / 2
    .node (Tree.build lo mid) mid (Tree.build (mid + 1) hi)
  else .leaf
termination_by hi - lo

def tripleAll {f : Type → Type} [Functor f] (x : f Nat) : f Nat := (· * 3) <$> x

/-! ## Driver -/

def main (args : List String) : IO UInt32 := do
  let n := (args.head?.bind String.toNat?).getD 10000000
  -- `sum` at five types, over the numbers below n in lists of 10000.
  let chunk := 10000
  let mut sNat : Nat := 0
  let mut sInt : Int := 0
  let mut sU64 : UInt64 := 0
  let mut sFloat : Float := 0.0
  let mut sV2 : V2 := 0
  let mut pU64 : UInt64 := 1
  for r in [0:(n + chunk - 1) / chunk] do
    let idx := List.range' (r * chunk) (min chunk (n - r * chunk))
    sNat := sNat + sum (idx.map (· * 3))
    sInt := sInt + sum (idx.map fun (i : Nat) => (↑i : Int) * (if i % 2 == 0 then 1 else -1))
    sU64 := sU64 + sum (idx.map fun i => (i.toUInt64 * 0x9E3779B97F4A7C15))
    sFloat := sFloat + sum (idx.map fun i => (i % 1000).toFloat / 8.0)
    sV2 := sV2 + sum (idx.map fun (i : Nat) => (⟨↑i, -(↑i : Int) * 2⟩ : V2))
    pU64 := Semigroup'.op pU64 (mconcat (idx.map (·.toUInt64 ||| 1)))
  IO.println s!"sum: Nat={sNat} Int={sInt} UInt64={sU64} Float={sFloat} V2={sV2}"
  let idx := List.range (min n 100000)

  -- `mconcat` and `mpow` at many instances.
  let small := idx.take 20
  IO.println s!"mconcat: Nat={mconcat (small.map (· + 1))} Int={mconcat (small.map (fun (i : Nat) => (↑i : Int) - 10))} UInt64={pU64} Float={mconcat [1.5, 2.0, -0.25]} String={mconcat ["ab", "", "çd", "e"]} List={mconcat [[1], [2, 3], [], [4]]}"
  IO.println s!"mconcat derived: pair={mconcat [(2, "x"), (3, "y"), (7, "z")]} option={repr (mconcat [some 2, none, some 5, some 1])} optionNone={repr (mconcat ([] : List (Option Nat)))} optionString={repr (mconcat [none, some "p", some "q"])}"
  let mut acc : UInt64 := 0
  for i in [0:n / 10] do
    acc := acc + mpow (i.toUInt64 + 3) (i % 64) + (fibMat (i % 90) : UInt64)
  IO.println s!"mpow: loop={acc} nat={mpow (3 : Nat) 200 % 1000000007} int={mpow (-7 : Int) 1000} float={mpow (1.0001 : Float) 10000} string={(mpow "ab" 5)} fibInt={(fibMat 300 : Int)} fibU64={(fibMat 300 : UInt64)}"

  -- Shapes: static dictionaries and packed ones.
  let circles := (idx.take 1000).map fun i => Circle.mk (i.toFloat / 10.0)
  let shapes : List AnyShape :=
    [⟨Circle.mk 1.0⟩, ⟨Rect.mk 2.0 3.5⟩, ⟨Poly.mk 6 2.0⟩, ⟨Circle.mk 0.5⟩, ⟨Rect.mk 1.0 1.0⟩]
  let mut manyArea := 0.0
  for i in [0:n / 10] do
    manyArea := manyArea + shapes[i % shapes.length]!.area
  IO.println s!"shapes: circles={totalPerimeter circles} describe={shapes.map (·.describe)} manyArea={manyArea}"

  -- outParam class and Functor.
  let bag : Bag := ⟨(idx.take 5000).toArray⟩
  let arr : Array Int := #[-5, 10, -15]
  let t := Tree.build 0 (min n 5000)
  IO.println s!"container: bag={containerSum bag} array={containerSum arr}"
  IO.println s!"functor: tree={sum (tripleAll t).toList} list={tripleAll [1, 2, 3]} option={tripleAll (some 14)} none={tripleAll (none : Option Nat)} array={tripleAll #[5, 6]}"
  pure 0
