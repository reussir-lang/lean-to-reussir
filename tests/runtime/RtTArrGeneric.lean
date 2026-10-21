/-! Runtime test (typed arrays, clean step B1: generic code), `RtCArrGeneric`
and `RtCArrColumn` at pointer kinds: arrays of a structure (`Pt`), of an
inductive with nullary constructors (`Shape`), of `Nat`, `String`,
`List Nat` and `Array Nat`, through
- user functions polymorphic in `α` that read and write an `Array α`
  (`@[noinline]`), class-generic folds, a `@[specialize]` fold, a
  monad-generic builder;
- function values of generic type (`through`, `twice`, a list of
  `Array α → Array α` values, a structure field `Op α`, a generic box
  `Wrap α` holding an array);
- existential packages (`Pack`: the element type is a field, so the array
  is an `Array lcAny` in Lean's compiled code), beside typed arrays of the
  same element types that never enter a package;
- polymorphic recursion (`nest`);
- a column whose element type depends on a value (`Column`, `Ty.denote`),
  updated through a match, one typed array put into it and one taken out
  and then updated by typed code.
What still reaches `lcAny` after lean2rr's instantiation keeps its kind
boxed (the whole-program check turns it off); the values must be the same
either way. -/

def mix (h x : UInt64) : UInt64 := (h ^^^ x) * 1099511628211
def strBits (s : String) : UInt64 := s.foldl (fun h c => mix h c.val.toUInt64) 3

structure Pt where
  n : Nat
  s : String
  deriving Repr, BEq, Inhabited

instance : ToString Pt := ⟨fun p => s!"<{p.n},{p.s}>"⟩

inductive Shape where
  | none
  | circle (r : Nat)
  | rect (w h : Nat)
  deriving Repr, BEq, Inhabited

instance : ToString Shape := ⟨fun | .none => "none" | .circle r => s!"c{r}" | .rect w h => s!"r{w}x{h}"⟩

class Bits (α : Type) where
  bits : α → UInt64

instance : Bits Pt := ⟨fun p => mix p.n.toUInt64 (strBits p.s)⟩
instance : Bits Shape := ⟨fun | .none => 1 | .circle r => mix 2 r.toUInt64 | .rect w h => mix (mix 3 w.toUInt64) h.toUInt64⟩
instance : Bits Nat := ⟨fun n => (n % 18446744073709551557).toUInt64⟩
instance : Bits String := ⟨strBits⟩
instance : Bits (List Nat) := ⟨fun l => l.foldl (fun h x => mix h x.toUInt64) 5⟩
instance : Bits (Array Nat) := ⟨fun a => a.foldl (fun h x => mix h x.toUInt64) 9⟩

@[noinline] def digest {α : Type} [Bits α] (a : Array α) : UInt64 :=
  a.foldl (fun h x => mix h (Bits.bits x)) 7

@[noinline] def rotateSwap {α : Type} [Inhabited α] (a : Array α) (k : Nat) : Array α := Id.run do
  let n := a.size
  if n == 0 then return a
  let mut r := a
  for i in [0:n] do
    r := r.set! i a[(i + k) % n]!
  for i in [0:n / 2] do
    r := r.swapIfInBounds (2 * i) (2 * i + 1)
  return r

@[noinline] def build {α : Type} (n : Nat) (f : Nat → α) : Array α := Id.run do
  let mut a := Array.emptyWithCapacity n
  for i in [0:n] do
    a := a.push (f i)
  return a

@[noinline] def dedupAdjacent {α : Type} [BEq α] (a : Array α) : Array α :=
  a.foldl (fun acc x => if acc.back? == some x then acc else acc.push x) #[]

@[specialize] def foldMap {α β : Type} (f : α → β) (g : β → β → β) (z : β) (a : Array α) : β :=
  a.foldl (fun acc x => g acc (f x)) z

def buildM {m : Type → Type} [Monad m] {α : Type} (n : Nat) (f : Nat → m α) : m (Array α) := do
  let mut a := #[]
  for i in [0:n] do
    a := a.push (← f i)
  return a

@[noinline] def through {α β : Type} (k : α → β) (x : α) : β := k x
@[noinline] def twice {α : Type} (f : α → α) : α → α := fun x => f (f x)
@[noinline] def applyAll {α : Type} (fs : List (α → α)) (x : α) : α := fs.foldl (fun acc f => f acc) x

structure Op (α : Type) where
  name : String
  run : Array α → Array α

structure Wrap (α : Type) where
  val : α
  tag : Nat

@[noinline] def runOps {α : Type} (ops : List (Op α)) (a : Array α) : Array α × List String :=
  ops.foldl (fun (acc, names) op => (op.run acc, names ++ [op.name])) (a, [])

structure Pack where
  α : Type
  arr : Array α
  inh : Inhabited α
  render : α → String
  bump : α → α
  bits : α → UInt64

def Pack.step (p : Pack) (i : Nat) : Pack :=
  have := p.inh
  { p with arr := (p.arr.push (p.bump p.arr[i % p.arr.size]!)).swapIfInBounds 0 (i % (p.arr.size + 1)) }

def Pack.digest (p : Pack) : UInt64 := p.arr.foldl (fun h x => mix h (p.bits x)) 7
def Pack.sample (p : Pack) : String := s!"{(p.arr.toList.take 3).map p.render}"

def stepAll (ps : Array Pack) : Nat → Nat → Array Pack
  | 0, _ => ps
  | k + 1, i => stepAll (ps.map (·.step i)) k (i + 1)

def mkPack {α : Type} [Inhabited α] [ToString α] [Bits α] (a : Array α) (bump : α → α) : Pack :=
  ⟨α, a, inferInstance, toString, bump, Bits.bits⟩

def nest : (d : Nat) → {α : Type} → (α → String) → Array α → String
  | 0, _, sh, a => s!"{a.size}:{a.toList.map sh}"
  | d + 1, _, sh, a => nest d (fun b => s!"<{b.toList.map sh}>") #[a, a.reverse.pop]

-- a column whose element type depends on a value
inductive Ty | pt | str | nat | shape deriving BEq, Repr

@[reducible] def Ty.denote : Ty → Type
  | .pt => Pt | .str => String | .nat => Nat | .shape => Shape

structure Column where
  ty : Ty
  data : Array ty.denote

instance : Inhabited Column := ⟨⟨.nat, #[]⟩⟩

def Ty.bits : (t : Ty) → t.denote → UInt64
  | .pt, x => Bits.bits x | .str, x => Bits.bits x | .nat, x => Bits.bits x | .shape, x => Bits.bits x

def Ty.mk : (t : Ty) → Nat → t.denote
  | .pt, i => { n := i, s := s!"c{i}" } | .str, i => s!"k{i}" | .nat, i => i * i + 2 ^ 64 | .shape, i => .circle i

def Column.digest (c : Column) : UInt64 := c.data.foldl (fun h x => mix h (c.ty.bits x)) 11

def Column.step (c : Column) (i : Nat) : Column :=
  match c with
  | ⟨.pt, d⟩ => ⟨.pt, ((d.push (Ty.mk .pt i)).set! (i % (d.size + 1)) { n := i + 1, s := "set" }).swapIfInBounds 0 1⟩
  | ⟨.str, d⟩ => ⟨.str, (d.push (Ty.mk .str i)).modify (i % (d.size + 1)) (· ++ "!")⟩
  | ⟨.nat, d⟩ => ⟨.nat, (d.push (Ty.mk .nat i)).pop.push i⟩
  | ⟨.shape, d⟩ => ⟨.shape, (d.push (.rect i 2)).reverse⟩

def toTypedStr (c : Column) : Array String :=
  match c with
  | ⟨.str, d⟩ => d
  | _ => #[]

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 20
  let pts : Array Pt := build n fun i => { n := i * 3, s := s!"p{i}" }
  let shs : Array Shape := build n fun i => if i % 3 == 0 then .none else if i % 3 == 1 then .circle i else .rect i (i + 1)
  let nats : Array Nat := build n fun i => if i % 4 == 0 then 2 ^ 70 + i else i
  let strs : Array String := build n fun i => s!"s{i}"
  let lsts : Array (List Nat) := build n fun i => List.range (i % 3)
  let arrs : Array (Array Nat) := build n fun i => Array.range (i % 4)
  IO.println s!"build {digest pts} {digest shs} {digest nats} {digest strs} {digest lsts} {digest arrs}"
  IO.println s!"rotate {digest (rotateSwap pts 3)} {digest (rotateSwap shs 1)} {digest (rotateSwap nats 5)} {digest (rotateSwap strs 2)} {digest (rotateSwap lsts 7)} {digest (rotateSwap arrs 4)}"
  IO.println s!"dedup {(dedupAdjacent (shs.map fun s => s == .none)).size} {(dedupAdjacent (lsts.map List.length)).size} {(dedupAdjacent strs).size}"
  IO.println s!"foldMap {foldMap Pt.n (· + ·) 0 pts} {foldMap String.length (· + ·) 0 strs} {foldMap (Bits.bits) mix 1 arrs}"
  let mio ← buildM n fun i => do pure s!"m{i}"
  let mid := Id.run (buildM n fun i => pure (Pt.mk i "id"))
  IO.println s!"buildM {digest mio} {digest mid}"
  let t1 : Array Pt := through (fun (a : Array Pt) => a.push { n := 99, s := "t" }) pts
  let t2 : Nat := through (fun (a : Array String) => a.size) strs
  let t3 : Array Nat := twice (fun (a : Array Nat) => a.map (· + 1) |>.push 0) nats
  let t4 : Array Shape := applyAll [(·.push .none), (·.reverse), (·.map fun | .circle r => .circle (r + 1) | s => s), (·.pop)] shs
  IO.println s!"fnvalues {digest t1} {t2} {digest t3} {digest t4}"
  let ops : List (Op String) := [⟨"push", (·.push "z")⟩, ⟨"rev", (·.reverse)⟩, ⟨"upper", (·.map String.toUpper)⟩]
  let (r, names) := runOps ops strs
  IO.println s!"ops {digest r} {names} {digest strs}"
  let w : Wrap (Array Pt) := ⟨pts, 1⟩
  let w2 : Wrap (Array Pt) := { w with val := w.val.push default }
  IO.println s!"wrap {digest w.val} {digest w2.val} {w2.tag}"
  let packs0 : Array Pack := #[mkPack pts (fun p => { p with n := p.n + 1 }), mkPack shs (fun _ => .none),
    mkPack nats (· * 3), mkPack strs (· ++ "+"), mkPack lsts (0 :: ·), mkPack arrs (·.push 1)]
  let packs := stepAll packs0 n 0
  let mut typedP : Array Pt := (Array.range n).map fun i => pts[i]!
  let mut typedS : Array String := (Array.range n).map fun i => strs[i]!
  for i in [0:n] do
    typedP := typedP.push { typedP[i % typedP.size]! with n := i }
    typedS := typedS.push (typedS[i % typedS.size]! ++ "+")
  IO.println s!"packs {packs.map Pack.digest} {packs.map (·.arr.size)}"
  IO.println s!"packs show {packs.map Pack.sample}"
  IO.println s!"typed {digest typedP} {digest typedS} {typedP.size}"
  IO.println s!"nest {nest 3 toString (pts.extract 0 3)}"
  IO.println s!"nest {nest 2 toString (strs.extract 4 7)}"
  -- columns
  let strCol : Column := ⟨.str, strs.extract 0 5⟩
  let mut cols : Array Column := #[⟨.pt, #[]⟩, strCol, ⟨.nat, #[1, 2 ^ 65]⟩, ⟨.shape, #[.none]⟩]
  for i in [0:n] do
    cols := cols.map (·.step i)
  let mut out := toTypedStr cols[1]!
  for i in [0:n] do
    out := out.push s!"o{i}" |>.modify 0 (· ++ ".")
  IO.println s!"columns {cols.map Column.digest} {cols.map (·.data.size)} {digest out} {out.size}"
