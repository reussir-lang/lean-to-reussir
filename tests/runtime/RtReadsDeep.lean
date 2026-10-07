/-! Runtime test: array reads deep in a function's branches, call sites that
LLVM judges cold, in loops. `tests/runtime/ffi-inline-check.sh` also builds
this test to LLVM IR and fails when a read's texture or function stays a
call (the read textures must stay under LLVM's inlining threshold for a
cold call site, Reussir issue 36). The read of a box,
`l2r_view_take<LAny>`, and the reads of a `Nat` or `Int` element at its
type, `l2r_view_take_as`, are over that threshold, and the patch 36-a is
parked: the check allows their calls here, and only here. Each `pick` reads
after seven conditions: `ByteArray`, `Array UInt64`, `Array Nat`, `Array
Int`, `Array` of a structure, `FloatArray`, at a proved index and with
`get!` (at the structure, a counted element: its default released after
the read, `l2r_consume`). -/

structure P where
  x : Nat
  y : UInt64
deriving Inhabited

@[noinline] def pickB (a : ByteArray) (i : Nat) (h : i < a.size) (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else
  if n % 3 = 0 then n / 3 + 1 else
  if n % 5 = 0 then n / 5 + 2 else
  if n % 7 = 0 then n / 7 + 3 else
  if n % 11 = 0 then n / 11 + 4 else
  if n % 13 = 0 then n / 13 + 5 else
  if n % 17 = 0 then n / 17 + 6 else
  (a[i]'h).toNat + (a.get! (i + 1)).toNat

@[noinline] def pickU (a : Array UInt64) (i : Nat) (h : i < a.size) (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else
  if n % 3 = 0 then n / 3 + 1 else
  if n % 5 = 0 then n / 5 + 2 else
  if n % 7 = 0 then n / 7 + 3 else
  if n % 11 = 0 then n / 11 + 4 else
  if n % 13 = 0 then n / 13 + 5 else
  if n % 17 = 0 then n / 17 + 6 else
  (a[i]'h).toNat + a[i + 1]!.toNat

@[noinline] def pickN (a : Array Nat) (b : Array Int) (i : Nat) (h : i < a.size) (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else
  if n % 3 = 0 then n / 3 + 1 else
  if n % 5 = 0 then n / 5 + 2 else
  if n % 7 = 0 then n / 7 + 3 else
  if n % 11 = 0 then n / 11 + 4 else
  if n % 13 = 0 then n / 13 + 5 else
  if n % 17 = 0 then n / 17 + 6 else
  a[i]'h + a[i + 1]! + b[i]!.natAbs

@[noinline] def pickP (a : Array P) (f : FloatArray) (i : Nat) (h : i < a.size) (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else
  if n % 3 = 0 then n / 3 + 1 else
  if n % 5 = 0 then n / 5 + 2 else
  if n % 7 = 0 then n / 7 + 3 else
  if n % 11 = 0 then n / 11 + 4 else
  if n % 13 = 0 then n / 13 + 5 else
  if n % 17 = 0 then n / 17 + 6 else
  (a[i]'h).x + (a[i]'h).y.toNat + a[i + 1]!.x + (f.get! i).toUInt64.toNat

def main (args : List String) : IO Unit := do
  let n := args.length + 64
  let b := ByteArray.mk ((Array.range n).map fun i => (i * 7 + 3).toUInt8)
  let u := (Array.range n).map fun i => (i * 11).toUInt64
  let an := (Array.range n).map fun i => if i % 9 = 0 then 2^64 + i else i
  let ai : Array Int := (Array.range n).map fun i => (Int.ofNat i) - (2^65 : Int)
  let ap := (Array.range n).map fun i => ({ x := i, y := (i * 3).toUInt64 } : P)
  let af : FloatArray := ⟨(Array.range n).map (·.toFloat)⟩
  let mut s := 0
  for k in [0:200000] do
    let i := k % (n - 1)
    if h : i < b.size then s := s + pickB b i h k
    if h : i < u.size then s := s + pickU u i h k
    if h : i < an.size then s := s + pickN an ai i h k
    if h : i < ap.size then s := s + pickP ap af i h k
  IO.println s!"sum {s}"
