/-! Runtime test (compact scalar arrays, hunt HCA-02): fields of generic
structures that hold arrays inside another type: `Array (Array α)`,
`List (Array α)`, `Option (Array α)`. The layout has them at `lcAny`
(`Array (Array lcAny)`, `List (Array lcAny)`), and a box holds each inner
array, so a compact array there is no crossing
(docs/implementation/representations/compact-arrays.md, "The whole-program
check turns a kind off"). Before, each such field turned its kind off
(`Matrix Float`: f64, `Rows UInt8`: u8, `Opt UInt64`: u64); now every kind
stays on (`L2R_DEBUG=1`).
- `Matrix Float` (`rows : Array (Array α)`): built, multiplied, read;
- `Rows UInt8` (`List (Array α)`), `Opt UInt64` (`Option (Array α)`, with
  a value from 2^63), `Grid UInt16` (`Array (List (Array α))`);
- a structure `Box1 α` with `Option (Array α)` read through a dependent
  type `B b` (`Box1 UInt64` or `Box1 Nat`): built in typed code in each
  branch, so the `UInt64` arrays stay compact. -/
structure Matrix (α : Type) where
  rows : Array (Array α)
  n : Nat

def Matrix.mul (a b : Matrix Float) : Matrix Float :=
  ⟨a.rows.map fun r => (Array.range (b.rows[0]!.size)).map fun j =>
    (Array.range r.size).foldl (fun s k => s + r[k]! * b.rows[k]![j]!) 0.0, a.n⟩

@[noinline] def ident (n : Nat) : Matrix Float :=
  ⟨(Array.range n).map fun i => (Array.range n).map fun j => if i == j then 2.0 else 0.5, n⟩

structure Rows (α : Type) where
  xs : List (Array α)
  k : Nat

structure Opt (α : Type) where
  o : Option (Array α)
  k : Nat

structure Grid (α : Type) where
  cells : Array (List (Array α))

@[noinline] def mkRows (n : Nat) : Rows UInt8 := ⟨(List.range n).map fun i => #[i.toUInt8, 7, 255], n⟩
@[noinline] def mkOpt (n : Nat) : Opt UInt64 := ⟨some #[n.toUInt64, 0x8000000000000000], n⟩
@[noinline] def mkGrid (n : Nat) : Grid UInt16 :=
  ⟨(Array.range n).map fun i => [#[i.toUInt16, 65535], #[]]⟩
@[noinline] def bumpRows (r : Rows UInt8) : Rows UInt8 := { r with xs := r.xs.map (·.push 1) }
@[noinline] def sumGrid (g : Grid UInt16) : Nat :=
  g.cells.foldl (fun s l => l.foldl (fun s a => a.foldl (fun s x => s + x.toNat) s) s) 0

structure Box1 (α : Type) where
  v : Option (Array α)

def B : Bool → Type
  | true => Box1 UInt64
  | false => Box1 Nat

@[noinline] def mkB (b : Bool) (n : Nat) : B b :=
  match b with
  | true => (⟨some #[n.toUInt64, 0x8000000000000000]⟩ : Box1 UInt64)
  | false => (⟨some #[n, n + 1]⟩ : Box1 Nat)

@[noinline] def useB (b : Bool) (x : B b) : Nat :=
  match b, x with
  | true, x => (x.v.map fun a => a.size + (a[1]!).toNat % 1000).getD 0
  | false, x => (x.v.map fun a => a.size + a[1]!).getD 0

def main : IO Unit := do
  let ms := [ident 3, ident 2]
  let ps := ms.map fun m => m.mul m
  IO.println s!"{ps.map (·.rows.map (·.toList))}"
  IO.println s!"{ps.map fun p => (p.rows.foldl (fun s r => r.foldl (· + ·) s) 0.0, p.n)}"
  let r := mkRows 3
  IO.println s!"{r.xs.map (·.toList)} {r.k} {(bumpRows r).xs.map (·.toList)}"
  let o := mkOpt 2
  IO.println s!"{o.o.map (·.toList)} {o.k}"
  let g := mkGrid 3
  IO.println s!"{g.cells.map (·.map (·.toList))} {sumGrid g}"
  IO.println s!"{useB true (mkB true 3)} {useB false (mkB false 3)}"
