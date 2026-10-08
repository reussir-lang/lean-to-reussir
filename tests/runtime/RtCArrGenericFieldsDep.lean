/-! Runtime test (compact scalar arrays, hunt HCA-02, the other side):
arrays inside another type (`List (Array α)`) built or read by code that
does not know the element type (`Array lcAny`: arrays of boxes), and read
or built at a scalar type elsewhere. A box in such a position holds the
compact array, which is no crossing, so the whole-program check must still
turn the kind off through the value's flow class
(docs/implementation/representations/compact-arrays.md): else an array of
boxes is unboxed as a compact one (a stop) or the reverse (a conversion
that the compact-array tests reject with `L2R_DEBUG_ARRAY_CONVERT=1`).
- A type-code universe whose codes denote lists of arrays: `rep` builds
  `List (Array t.denote)` (arrays of boxes), `len` reads it at `UInt64`
  in one branch (u64 off).
- An existential payload `List (Array α)` stored at `UInt8` and `Float`
  and read by `sizes`, which does not know `α` (u8 and f64 off).
- A dependent pair whose `List (Array (E b))` is built by generic code and
  read at `UInt16` in a branch (u16 off). -/
inductive Ty | u64 | nat | arr (t : Ty) | list (t : Ty)

@[reducible] def Ty.denote : Ty → Type
  | .u64 => UInt64
  | .nat => Nat
  | .arr t => Array t.denote
  | .list t => List t.denote

@[noinline] def rep (t : Ty) (n : Nat) (x : t.denote) : (Ty.list (Ty.arr t)).denote :=
  List.replicate 2 (Array.replicate n x)

@[noinline] def len (t : Ty) (v : t.denote) : Nat :=
  match t, v with
  | .list (.arr .u64), v => match v with
    | a :: _ => a.size + (a[1]!).toNat % 1000
    | [] => 0
  | .list (.arr .nat), v => match v with
    | a :: _ => a.size + a[1]!
    | [] => 0
  | _, _ => 0

@[noinline] def go (t : Ty) (x : t.denote) : Nat := len (.list (.arr t)) (rep t 3 x)

structure Sized where
  α : Type
  xs : List (Array α)
  k : Nat

@[noinline] def mkS (b : Bool) : Sized :=
  if b then ⟨UInt8, [#[1, 2, 3], #[4]], 1⟩ else ⟨Float, [#[1.5], #[2.5, 3.5]], 2⟩

@[noinline] def sizes (s : Sized) : List Nat := s.xs.map (·.size)

@[reducible] def E : Bool → Type
  | true => UInt16
  | false => Nat

structure Tagged where
  b : Bool
  xs : List (Array (E b))

@[noinline] def mkT (b : Bool) (x : E b) (n : Nat) : Tagged := ⟨b, List.replicate 2 (Array.replicate n x)⟩

@[noinline] def useT (t : Tagged) : Nat :=
  match t with
  | ⟨true, xs⟩ => match xs with
    | a :: _ => a.size + (a[1]!).toNat
    | [] => 0
  | ⟨false, xs⟩ => match xs with
    | a :: _ => a.size + a[1]!
    | [] => 0

@[noinline] def mkT16 (n : Nat) : Tagged := ⟨true, [Array.replicate n (65535 : UInt16)]⟩

def main : IO Unit := do
  IO.println s!"{go .u64 (0x8000000000000005 : UInt64)} {go .nat (7 : Nat)}"
  IO.println s!"{sizes (mkS true)} {sizes (mkS false)}"
  IO.println s!"{useT (mkT true (7 : UInt16) 3)} {useT (mkT false (7 : Nat) 3)} {useT (mkT16 4)}"
