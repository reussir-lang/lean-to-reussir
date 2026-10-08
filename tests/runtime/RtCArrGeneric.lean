/-! Runtime test (compact scalar arrays, plan "Not changed": generic code):
- user functions polymorphic in `α` that read and write an `Array α`
  (`rotateSwap`, `build`, `dedupAdjacent`; `@[noinline]`, not specialized
  by Lean), class-generic folds (`sumArr`, `maxArr`, `digest` over a user
  class), a `@[specialize]` fold, and a monad-generic builder, applied at
  scalar types of every storage kind;
- arrays passed through function values of generic type (`through`,
  `twice`, a list of `Array α → Array α` values, a structure field
  `Op α`, a generic box `Wrap α` holding an array);
- existential packages (`Pack`: the element type is a field, so the array
  is an `Array lcAny` in Lean's compiled code) built from typed arrays,
  updated by code that does not know the element type, beside typed
  arrays of the same kinds that never enter a package;
- polymorphic recursion (`nest`: `Array α` becomes `Array (Array α)` at
  each level, starting at `Array UInt8` and at `Array Float`).
Generic code that still reaches `lcAny` after lean2rr's instantiation
stays boxed under the plan; the values must be the same either way. -/

def mix (h x : UInt64) : UInt64 := (h ^^^ x) * 1099511628211

class Bits (α : Type) where
  bits : α → UInt64

instance : Bits UInt8 := ⟨(·.toUInt64)⟩
instance : Bits Bool := ⟨fun b => if b then 1 else 2⟩
instance : Bits UInt16 := ⟨(·.toUInt64)⟩
instance : Bits UInt32 := ⟨(·.toUInt64)⟩
instance : Bits Char := ⟨(·.val.toUInt64)⟩
instance : Bits UInt64 := ⟨id⟩
instance : Bits USize := ⟨(·.toUInt64)⟩
instance : Bits Float32 := ⟨(·.toBits.toUInt64)⟩
instance : Bits Float := ⟨Float.toBits⟩

@[noinline] def digest {α : Type} [Bits α] (a : Array α) : UInt64 :=
  a.foldl (fun h x => mix h (Bits.bits x)) 7

/-- Reads `a` and writes a rotated copy, then swaps pairs in place. -/
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

@[noinline] def sumArr {α : Type} [Add α] [OfNat α 0] (a : Array α) : α := a.foldl (· + ·) 0

@[noinline] def maxArr {α : Type} [Max α] [Inhabited α] (a : Array α) : α := a.foldl max a[0]!

@[specialize] def foldMap {α β : Type} (f : α → β) (g : β → β → β) (z : β) (a : Array α) : β :=
  a.foldl (fun acc x => g acc (f x)) z

def buildM {m : Type → Type} [Monad m] {α : Type} (n : Nat) (f : Nat → m α) : m (Array α) := do
  let mut a := #[]
  for i in [0:n] do
    a := a.push (← f i)
  return a

-- function values of generic type
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

-- existential packages
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
def Pack.sample (p : Pack) : String := s!"{(p.arr.toList.take 4).map p.render}"

/-- n steps of every package (a function: `Pack` lives in `Type 1`, so it cannot be an `IO` loop's state). -/
def stepAll (ps : Array Pack) : Nat → Nat → Array Pack
  | 0, _ => ps
  | k + 1, i => stepAll (ps.map (·.step i)) k (i + 1)

def mkPack {α : Type} [Inhabited α] [ToString α] [Bits α] (a : Array α) (bump : α → α) : Pack :=
  ⟨α, a, inferInstance, toString, bump, Bits.bits⟩

-- polymorphic recursion: the element type grows at each level
def nest : (d : Nat) → {α : Type} → (α → String) → Array α → String
  | 0, _, sh, a => s!"{a.size}:{a.toList.map sh}"
  | d + 1, _, sh, a => nest d (fun b => s!"<{b.toList.map sh}>") #[a, a.reverse.pop]

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 24
  -- typed arrays of each kind
  let u8 : Array UInt8 := build n fun i => (i * 37 + 1).toUInt8
  let bo : Array Bool := build n fun i => i % 3 == 0
  let u16 : Array UInt16 := build n fun i => (i * 7919).toUInt16
  let u32 : Array UInt32 := build n fun i => (i * 2654435761).toUInt32
  let ch : Array Char := build n fun i => Char.ofNat (0x1F300 + i)
  let u64 : Array UInt64 := build n fun i => i.toUInt64 * 0x9E3779B97F4A7C15 ||| 0x8000000000000000
  let us : Array USize := build n fun i => (i * 0x9E3779B97F4A7C15).toUSize
  let f32 : Array Float32 := build n fun i => (i.toFloat / 3.0 - 2.0).toFloat32
  let f64 : Array Float := build n fun i => if i == 5 then 0.0 / 0.0 else if i == 6 then -0.0 else i.toFloat / 7.0 - 1.0
  IO.println s!"build {digest u8} {digest bo} {digest u16} {digest u32} {digest ch} {digest u64} {digest us} {digest f32} {digest f64}"
  -- generic readers and writers
  IO.println s!"rotate {digest (rotateSwap u8 3)} {digest (rotateSwap bo 1)} {digest (rotateSwap u16 5)} {digest (rotateSwap u32 2)} {digest (rotateSwap ch 7)} {digest (rotateSwap u64 4)} {digest (rotateSwap us 9)} {digest (rotateSwap f32 6)} {digest (rotateSwap f64 8)}"
  IO.println s!"sources {digest u8} {digest u64} {digest f64}"
  IO.println s!"dedup {(dedupAdjacent (u8.map (· / 64))).size} {(dedupAdjacent bo).size} {(dedupAdjacent (f64.map (·.floor))).size} {(dedupAdjacent (ch.map Char.isAlpha)).size}"
  IO.println s!"sum {sumArr u8} {sumArr u16} {sumArr u32} {sumArr u64} {sumArr us} {sumArr f32} {sumArr f64}"
  IO.println s!"max {maxArr u8} {maxArr u16} {maxArr u32} {maxArr u64} {maxArr us} {maxArr f32} {maxArr f64}"
  IO.println s!"foldMap {foldMap (·.toNat) (· + ·) 0 u8} {foldMap (fun b => if b then 1 else 0) (· + ·) 0 bo} {foldMap Float.toBits mix 1 f64}"
  let mio ← buildM n fun i => do pure (i.toUInt16 * 3)
  let mid := Id.run (buildM n fun i => pure (i.toFloat.toFloat32))
  IO.println s!"buildM {digest mio} {digest mid}"
  -- arrays through function values of generic type
  let t1 : Array UInt64 := through (fun (a : Array UInt64) => a.push 0xFFFFFFFFFFFFFFFF) u64
  let t2 : Nat := through (fun (a : Array Float) => a.size) f64
  let t3 : Array UInt8 := twice (fun (a : Array UInt8) => a.map (· + 1) |>.push 0) u8
  let t4 : Array Float := applyAll [(·.push 1.5), (·.reverse), (·.map (· * 2)), (·.pop)] f64
  let t5 : Array Bool := applyAll [(·.map not), (·.push true), (·.swapIfInBounds 0 1)] bo
  IO.println s!"fnvalues {digest t1} {t2} {digest t3} {digest t4} {digest t5}"
  let ops : List (Op Char) := [⟨"push", (·.push 'z')⟩, ⟨"rev", (·.reverse)⟩, ⟨"upper", (·.map Char.toUpper)⟩]
  let (r, names) := runOps ops ch
  let opsU : List (Op USize) := [⟨"shl", (·.map (fun (x : USize) => x <<< 1))⟩, ⟨"set", (·.set! 0 7)⟩]
  let (ru, _) := runOps opsU us
  IO.println s!"ops {digest r} {names} {digest ru} {digest us}"
  let w : Wrap (Array UInt32) := ⟨u32, 1⟩
  let w2 : Wrap (Array UInt32) := { w with val := w.val.push 5 }
  IO.println s!"wrap {digest w.val} {digest w2.val} {w2.tag}"
  -- existential packages, beside typed arrays of the same kinds
  let packs0 : Array Pack := #[mkPack u8 (· * 3), mkPack bo not, mkPack u16 (· + 1000),
    mkPack u32 (fun (x : UInt32) => x >>> 1), mkPack ch (fun c => Char.ofNat (c.toNat + 1)),
    mkPack u64 (fun (x : UInt64) => x ^^^ 0xFF), mkPack us (· + 1), mkPack f32 (· * 2), mkPack f64 (· - 0.25)]
  let packs := stepAll packs0 n 0
  let mut typed8 : Array UInt8 := (Array.range n).map fun i => u8[i]!
  let mut typedF : Array Float := (Array.range n).map fun i => f64[i]!
  for i in [0:n] do
    typed8 := typed8.push (typed8[i % typed8.size]! * 3)
    typedF := typedF.push (typedF[i % typedF.size]! - 0.25)
  IO.println s!"packs {packs.map Pack.digest} {packs.map (·.arr.size)}"
  IO.println s!"packs show {packs.map Pack.sample}"
  IO.println s!"typed {digest typed8} {digest typedF} {typed8.size}"
  -- polymorphic recursion
  IO.println s!"nest {nest 3 toString (u8.extract 0 3)}"
  IO.println s!"nest {nest 2 toString (f64.extract 4 7)}"
