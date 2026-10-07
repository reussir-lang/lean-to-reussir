import Std.Data.HashSet
/-! Runtime test: existentials and dependent pairs. Values whose type is a
field of a structure, or is selected by another value, are built, stored,
changed in a loop and read back, and every result is printed:
- `Pkg`: a structure with a field `α : Type`, a value of it and a printer;
  a list of packages of nine types, mapped by code over the unknown type;
- `Sigma` with a type-valued first component (`(t : Ty) × t.denote`), a
  `PSigma` over the same family and one with a proof, and `Σ α : Type, α ×
  (α → String)`;
- `Column`: a structure whose array's element type depends on a field
  (`Array ty.denote`), for eight element types, pushed, read, set and
  folded in a loop;
- `Dynamic` values of user and library types with `TypeName`, read with
  `Dynamic.get?` at the right and at wrong types;
- packages that carry their own dictionaries (`ToString`, `BEq`,
  `Hashable`): a set built in code over the unknown type, with the hashes.
Argument: N (default 40), the length of the loops. -/

inductive Ty | nat | str | float | u64 | bool | list | pair | fn
  deriving Repr, BEq, Inhabited

@[reducible] def Ty.denote : Ty → Type
  | .nat => Nat
  | .str => String
  | .float => Float
  | .u64 => UInt64
  | .bool => Bool
  | .list => List Nat
  | .pair => Nat × String
  | .fn => Nat → Nat

def Ty.all : List Ty := [.nat, .str, .float, .u64, .bool, .list, .pair, .fn]

/-- A value of `t.denote` made from `i`. -/
@[noinline] def Ty.mk : (t : Ty) → Nat → t.denote
  | .nat, i => i * 3
  | .str, i => s!"s{i}"
  | .float, i => i.toFloat / 4
  | .u64, i => (i.toUInt64 <<< 60) + 0xFFFFFFFFFFFFFF00
  | .bool, i => i % 3 == 0
  | .list, i => List.range (i % 5)
  | .pair, i => (i, s!"p{i}")
  | .fn, i => (· + i)

/-- A printout of a value of `t.denote` that depends on all of it. -/
@[noinline] def Ty.show : (t : Ty) → t.denote → String
  | .nat, v => toString v
  | .str, v => v
  | .float, v => toString v
  | .u64, v => toString v
  | .bool, v => toString v
  | .list, v => toString v
  | .pair, v => toString v
  | .fn, f => s!"fn {f 100}"

-- Existential packages.
structure Pkg where
  α : Type
  val : α
  fmt : α → String

@[noinline] def Pkg.show (p : Pkg) : String := p.fmt p.val

/-- Code over the unknown type: applies a function of the package's own type. -/
@[noinline] def Pkg.twice (p : Pkg) (f : p.α → p.α) : Pkg := ⟨p.α, f (f p.val), p.fmt⟩

def pkgs (i : Nat) : List Pkg :=
  [⟨Nat, i, toString⟩, ⟨String, s!"x{i}", id⟩, ⟨Float, i.toFloat, toString⟩,
   ⟨UInt64, i.toUInt64 - 1, toString⟩, ⟨Bool, i % 2 == 0, toString⟩, ⟨Unit, (), fun _ => "unit"⟩,
   ⟨List String, ["a", toString i], toString⟩, ⟨Int, -(i : Int) - 2147483648, toString⟩,
   ⟨Char, Char.ofNat (0x1F600 + i), fun c => c.toString ++ toString c.toNat⟩]

-- Dependent pairs.
@[noinline] def entries (i : Nat) : List ((t : Ty) × t.denote) := Ty.all.map fun t => ⟨t, t.mk i⟩

@[noinline] def showEntry (e : (t : Ty) × t.denote) : String := e.1.show e.2

@[noinline] def psEntries (i : Nat) : List ((t : Ty) ×' t.denote) := Ty.all.map fun t => ⟨t, t.mk (i + 1)⟩

@[noinline] def positives (n : Nat) : List ((k : Nat) ×' k > 0) :=
  (List.range n).map fun k => ⟨k + 1, Nat.succ_pos k⟩

@[noinline] def typed (i : Nat) : List ((α : Type) × (α × (α → String))) :=
  [⟨Nat, (i, toString)⟩, ⟨String, (s!"t{i}", fun s => s ++ s)⟩, ⟨Float × Nat, ((0.5, i), toString)⟩]

-- A column whose element type is a field.
structure Column where
  ty : Ty
  data : Array ty.denote

@[noinline] def Column.push (c : Column) (i : Nat) : Column := ⟨c.ty, c.data.push (c.ty.mk i)⟩

/-- Sets element `j` to the value of `i`, in place when the array is unique. -/
@[noinline] def Column.set (c : Column) (j i : Nat) : Column :=
  match c with
  | ⟨t, d⟩ => ⟨t, d.set! j (t.mk i)⟩

@[noinline] def Column.render (c : Column) : String :=
  c.data.foldl (fun s v => s ++ c.ty.show v ++ ",") s!"{repr c.ty}:"

/-- A typed fold for two of the element types. -/
@[noinline] def Column.sum (c : Column) : Nat :=
  match c with
  | ⟨.nat, d⟩ => d.foldl (· + ·) 0
  | ⟨.list, d⟩ => d.foldl (fun s l => s + l.length) 0
  | ⟨.pair, d⟩ => d.foldl (fun s p => s + p.1 + p.2.length) 0
  | ⟨.fn, d⟩ => d.foldl (fun s f => f s) 0
  | ⟨t, d⟩ => d.size + (if t == .bool then 1 else 0)

-- Dynamic values.
structure Pt where
  x : UInt64
  y : Float
  deriving TypeName

structure Named where
  name : String
  tags : List Nat
  deriving TypeName

deriving instance TypeName for Float
deriving instance TypeName for String

@[noinline] def dyns (i : Nat) : Array Dynamic :=
  #[.mk (Pt.mk i.toUInt64 2.5), .mk (3.25 + i.toFloat : Float), .mk s!"str{i}",
    .mk (Named.mk "nm" (List.range (i % 4))), .mk (Pt.mk 0xFFFFFFFFFFFFFFFF (-0.0))]

@[noinline] def readDyn (d : Dynamic) : String :=
  match d.get? Pt, d.get? Float, d.get? String, d.get? Named with
  | some p, _, _, _ => s!"Pt {p.x} {p.y}"
  | _, some f, _, _ => s!"Float {f}"
  | _, _, some s, _ => s!"String {s}"
  | _, _, _, some n => s!"Named {n.name} {n.tags}"
  | _, _, _, _ => s!"? {d.typeName}"

-- Packages with their own dictionaries.
structure Bag where
  α : Type
  [instBeq : BEq α]
  [instHash : Hashable α]
  [instStr : ToString α]
  xs : List α

/-- Code over the unknown type: the distinct elements, with the package's
own `BEq` and `Hashable`. -/
@[noinline] def Bag.distinct (b : Bag) : Nat × UInt64 :=
  let _ := b.instBeq; let _ := b.instHash
  let s : Std.HashSet b.α := b.xs.foldl (fun s x => s.insert x) {}
  (s.size, b.xs.foldl (fun h x => mixHash h (Hashable.hash x)) 7)

@[noinline] def Bag.show (b : Bag) : String :=
  let _ := b.instStr
  b.xs.foldl (fun s x => s ++ toString x ++ " ") ""

def bags (n : Nat) : List Bag :=
  [⟨Nat, (List.range n).map (· % 7)⟩, ⟨String, (List.range n).map (s!"k{· % 5}")⟩,
   ⟨Nat × String, (List.range n).map fun i => (i % 3, s!"v{i % 2}")⟩,
   ⟨List Nat, (List.range n).map fun i => List.range (i % 4)⟩,
   ⟨Int, (List.range n).map fun (i : Nat) => Int.ofNat i * -1000000007 % 9223372036854775807⟩]

def main (args : List String) : IO Unit := do
  let n := (args.headD "40").toNat!
  -- packages
  let mut acc := ""
  for i in [0:n] do
    for p in pkgs i do acc := acc ++ p.show ++ ";"
  IO.println s!"pkgs {acc.length} {acc.take 200}"
  IO.println ((pkgs 3).map Pkg.show)
  let p := Pkg.twice ⟨Nat, 5, toString⟩ (· * 10)
  let q := Pkg.twice ⟨String, "ab", toString⟩ (· ++ "!")
  IO.println s!"twice {p.show} {q.show}"
  -- dependent pairs
  let mut out := 0
  for i in [0:n] do
    for e in entries i do out := out + (showEntry e).length
  IO.println s!"sigma {out} {(entries 7).map showEntry}"
  IO.println s!"psigma {(psEntries 2).map fun e => e.1.show e.2}"
  IO.println s!"positives {(positives n).foldl (fun s e => s + e.1) 0}"
  IO.println s!"typed {(typed 9).map fun e => e.2.2 e.2.1}"
  -- columns
  let mut cols : Array Column := Ty.all.toArray.map fun t => ⟨t, #[]⟩
  for i in [0:n] do
    cols := cols.map (·.push i)
    if i % 3 == 2 then cols := cols.map (·.set (i / 2) (i * 7))
  IO.println s!"columns {cols.map (·.sum)} {cols.map (·.data.size)}"
  for c in cols do IO.println (c.render.take 120)
  -- Dynamic
  for i in [0:3] do
    IO.println ((dyns i).toList.map readDyn)
  let names := (dyns 1).map (·.typeName)
  IO.println s!"names {names}"
  let d0 := dyns 0
  let at_ (i : Nat) : Dynamic := d0.getD i (.mk "none")
  IO.println s!"wrong {((at_ 0).get? Float).isSome} {((at_ 1).get? Pt).isSome} {((at_ 3).get? String).isSome} {((at_ 3).get? Named).isSome}"
  -- bags
  for b in bags n do
    IO.println s!"bag {b.distinct} {b.show.take 60}"
