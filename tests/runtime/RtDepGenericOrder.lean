import Std.Data.HashMap
/-! Runtime test: scalar values compared, sorted, hashed and added by generic
code, which receives them where their type is not known and calls the
type's own functions on them: `Array.qsort` and `List.mergeSort` with
`<`, `List.max?`/`min?`, `BEq` (`contains`, `eraseDups`), `Std.HashMap`
keys, `Hashable`, and a generic sum with the type's `+` (wrapping for the
fixed-width types). Values: `UInt64` on both sides of 2^63 (a box that
holds small values in place and large ones in a cell must compare them as
numbers), `USize`, `UInt8`, `Int` (negative, around ±2^31 and ±2^63, large),
`Nat` (around 2^63 and 2^64), `Float` (−0.0 and 0.0, which are equal, ±inf,
subnormals; the sums add the finite values only, as the bits of a NaN made
by arithmetic differ between platforms), `Float32`, `Char`, `String`,
pairs. Native Lean prints the results. -/

/-- A generic sort, not specialized by Lean: the comparison is a value. -/
@[noinline] def sortBy {α : Type} (lt : α → α → Bool) (xs : Array α) : Array α := xs.qsort lt

@[noinline] def msortBy {α : Type} (le : α → α → Bool) (xs : List α) : List α := xs.mergeSort le

@[noinline] def maxBy {α : Type} (lt : α → α → Bool) : List α → Option α
  | [] => none
  | x :: xs => some (xs.foldl (fun m y => if lt m y then y else m) x)

@[noinline] def countEq {α : Type} (eq : α → α → Bool) (x : α) (xs : List α) : Nat :=
  xs.foldl (fun n y => if eq x y then n + 1 else n) 0

@[noinline] def dedup {α : Type} (eq : α → α → Bool) (xs : List α) : List α :=
  xs.foldl (fun acc y => if acc.any (eq y) then acc else acc ++ [y]) []

@[noinline] def sumBy {α : Type} (add : α → α → α) (z : α) (xs : List α) : α := xs.foldl add z

@[noinline] def hashAll {α : Type} (h : α → UInt64) (xs : List α) : UInt64 :=
  xs.foldl (fun acc x => mixHash acc (h x)) 11

@[noinline] def tally {α : Type} [BEq α] [Hashable α] (xs : List α) : List (α × Nat) :=
  let m : Std.HashMap α Nat := xs.foldl (fun m x => m.insert x (m.getD x 0 + 1)) {}
  xs.filterMap fun x => (m.get? x).map (x, ·)

def run {α : Type} [ToString α] [BEq α] [Hashable α] (name : String) (lt : α → α → Bool)
    (add : α → α → α) (z : α) (xs : List α) : IO Unit := do
  IO.println s!"{name} sorted {sortBy lt xs.toArray}"
  IO.println s!"{name} msorted {msortBy (fun a b => !lt b a) xs}"
  IO.println s!"{name} max {maxBy lt xs} min {maxBy (fun a b => lt b a) xs}"
  IO.println s!"{name} count {xs.map (countEq (· == ·) · xs)} dedup {dedup (· == ·) xs}"
  IO.println s!"{name} sum {sumBy add z xs} hash {hashAll hash xs}"
  IO.println s!"{name} tally {(tally xs).take 4}"

def u64s : List UInt64 :=
  [18446744073709551615, 0, 9223372036854775808, 9223372036854775807, 1, 9223372036854775809,
   12345678901234567890, 9223372036854775808, 42]

def ints : List Int :=
  [-1, 2147483647, -2147483648, 2147483648, -2147483649, -9223372036854775808, 9223372036854775807,
   9223372036854775808, -9223372036854775809, -(10 ^ 30), 10 ^ 30, 0, -1]

def nats : List Nat := [2 ^ 64, 9223372036854775807, 9223372036854775808, 0, 2 ^ 63 - 2, 2 ^ 64 + 1, 7]

def floats : List Float :=
  [0.0, -0.0, 1.5, -1.5, Float.ofBits 1, Float.ofBits 0x8000000000000001, Float.ofBits 0x7ff0000000000000,
   Float.ofBits 0xfff0000000000000, 1e308, -1e-308, 0.0]

def main : IO Unit := do
  run "u64" (· < ·) (· + ·) 0 u64s
  run "usize" (· < ·) (· + ·) 0 (u64s.map UInt64.toUSize)
  run "u8" (· < ·) (· + ·) 0 [255, 0, 128, 127, 1, 200, 128]
  run "int" (· < ·) (· + ·) 0 ints
  run "nat" (· < ·) (· + ·) 0 nats
  run "char" (· < ·) (fun a _ => a) 'a' ['z', 'a', Char.ofNat 0x10FFFF, Char.ofNat 0xE000, 'é', 'a']
  run "string" (· < ·) (· ++ ·) "" ["b", "a", "", "ab", "é", "b"]
  -- floats: `==` is IEEE equality (−0.0 == 0.0); hashed by their bits
  let fs := floats
  IO.println s!"float sorted {(sortBy (· < ·) fs.toArray).map Float.toBits}"
  IO.println s!"float max {(maxBy (· < ·) fs).map Float.toBits} min {(maxBy (fun a b => b < a) fs).map Float.toBits}"
  IO.println s!"float count {fs.map (countEq (· == ·) · fs)} dedup {(dedup (· == ·) fs).map Float.toBits}"
  IO.println s!"float sum {(sumBy (· + ·) 0 (fs.filter (·.isFinite))).toBits} hash {hashAll (fun x => hash x.toBits) fs}"
  let gs : List Float32 := fs.map Float.toFloat32
  IO.println s!"float32 sorted {(sortBy (· < ·) gs.toArray).map Float32.toBits}"
  IO.println s!"float32 count {gs.map (countEq (· == ·) · gs)} sum {(sumBy (· + ·) 0 (gs.filter (·.isFinite))).toBits}"
  -- pairs, compared lexicographically by a generic function
  let ps : List (UInt64 × Int) := u64s.zip ints
  let lexLt : UInt64 × Int → UInt64 × Int → Bool := fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)
  IO.println s!"pairs sorted {sortBy lexLt ps.toArray}"
  IO.println s!"pairs tally {(tally ps).take 3} hash {hashAll hash ps}"
