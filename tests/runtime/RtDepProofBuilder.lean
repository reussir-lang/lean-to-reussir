/-! Runtime test: generic code used at a proposition (blowup audit BA-18;
branch fix-proof-builder's RtProofBuilder). A type argument that is a
proposition or a predicate carries no data (`WL (3 < 5)`: every `val` is
a proof), and at data (`WL Nat`) the same structures hold numbers. Each
builder makes a list of N in O(N) natively, at both. A translation that
gives the proof instantiation another representation than the code that
builds the list can convert the list built so far at every level
(8010044 allocations for 4000 elements, at `Nat` 8039). Shapes: a
structure over `Sort u` (`Wrap`), `PLift`, `PProd`, a mutual pair of
builders, a tail-recursive builder, a consumer called once per element,
`PSigma` with a predicate and with a type family, and a function taking a
proposition and its `Decidable` instance. The output is checked here; the
allocations by tests/runtime/alloc-check.sh (RtDepProofBuilder.alloc).
Argument: N (default 2000). -/

structure Wrap (α : Sort u) where
  val : α
  tag : Nat

inductive WL (α : Sort u) where
  | nil
  | cons (w : Wrap α) (r : WL α)

@[noinline] def sumTags {α : Sort u} : WL α → Nat
  | .nil => 0
  | .cons w ws => w.tag + sumTags ws

def mkWL {α : Sort u} (f : Nat → Wrap α) : Nat → WL α
  | 0 => .nil
  | k + 1 => .cons (f k) (mkWL f k)

mutual
def mkA {α : Sort u} (f : Nat → Wrap α) : Nat → WL α
  | 0 => .nil
  | k + 1 => .cons (f k) (mkB f k)
def mkB {α : Sort u} (f : Nat → Wrap α) : Nat → WL α
  | 0 => .nil
  | k + 1 => .cons (f (k + 1)) (mkA f k)
end

def mkT {α : Sort u} (f : Nat → Wrap α) (acc : WL α) : Nat → WL α
  | 0 => acc
  | k + 1 => mkT f (.cons (f k) acc) k

-- a monomorphic builder: the list is made at its own (erased) type
def mkProofs : Nat → WL (3 < 5)
  | 0 => .nil
  | k + 1 => .cons ⟨by decide, k⟩ (mkProofs k)

def mkPL {α : Sort u} (f : Nat → α) : Nat → List (PLift α)
  | 0 => []
  | k + 1 => ⟨f k⟩ :: mkPL f k

inductive PPL (α : Sort u) where
  | nil
  | cons (p : PProd α Nat) (r : PPL α)

def mkPP {α : Sort u} (f : Nat → α) : Nat → PPL α
  | 0 => .nil
  | k + 1 => .cons ⟨f k, k⟩ (mkPP f k)

@[noinline] def sumPP {α : Sort u} : PPL α → Nat
  | .nil => 0
  | .cons p ps => p.2 + sumPP ps

inductive SL {α : Sort u} (β : α → Sort v) where
  | nil
  | cons (p : PSigma β) (r : SL β)

def mkSL {α : Sort u} {β : α → Sort v} (f : Nat → PSigma β) : Nat → SL β
  | 0 => .nil
  | k + 1 => .cons (f k) (mkSL f k)

@[noinline] def lenSL {α : Sort u} {β : α → Sort v} : SL β → Nat
  | .nil => 0
  | .cons _ r => 1 + lenSL r

@[noinline] def sumFst {β : Nat → Sort v} : SL β → Nat
  | .nil => 0
  | .cons p r => p.1 + sumFst r

@[noinline] def countIf (p : Nat → Prop) [DecidablePred p] : List Nat → Nat
  | [] => 0
  | x :: xs => (if p x then 1 else 0) + countIf p xs

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 2000
  -- `Wrap` at a proposition and at `Nat`
  let ps : WL (3 < 5) := mkWL (fun i => ⟨by decide, i + 1⟩) n
  let ds : WL Nat := mkWL (fun i => ⟨i * 10, i⟩) n
  IO.println s!"mkWL proof {sumTags ps} data {sumTags ds}"
  -- a mutual pair and a tail-recursive builder
  let ms : WL (3 < 5) := mkA (fun i => ⟨by decide, i⟩) n
  let md : WL Nat := mkA (fun i => ⟨i, i⟩) n
  let ts : WL (3 < 5) := mkT (fun i => ⟨by decide, i⟩) .nil n
  IO.println s!"mutual proof {sumTags ms} data {sumTags md} tail proof {sumTags ts}"
  -- a generic consumer at a proposition, called once per element
  let qs := mkProofs n
  let mut s := 0
  for i in [0:n] do s := s + sumTags qs % (i + 7)
  IO.println s!"consumer {s}"
  -- library structures over `Sort u`
  let pl : List (PLift (3 < 5)) := mkPL (fun _ => by decide) n
  let pp : PPL (3 < 5) := mkPP (fun _ => by decide) n
  let pd : PPL Nat := mkPP (fun i => i) n
  IO.println s!"PLift {pl.length} PProd proof {sumPP pp} data {sumPP pd}"
  -- `PSigma` whose second component is a proof, and one whose is data
  let sp : SL (fun k : Nat => k < n + 1) := mkSL (fun i => ⟨i % (n + 1), Nat.mod_lt _ (by omega)⟩) n
  let sd : SL (fun _ : Nat => String) := mkSL (fun i => ⟨i, toString i⟩) n
  IO.println s!"PSigma proof {lenSL sp} {sumFst sp} data {lenSL sd} {sumFst sd}"
  -- a proposition and its `Decidable` instance as arguments
  let xs := List.range n
  IO.println s!"countIf {countIf (· % 3 = 0) xs} {countIf (fun x => x < 10 ∧ x % 2 = 1) xs}"
