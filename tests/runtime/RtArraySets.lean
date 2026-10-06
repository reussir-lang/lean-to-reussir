/-! Runtime test: array sets in loops, at ordinary call sites (one condition
before each). `tests/runtime/ffi-inline-check.sh` also builds this test to
LLVM IR and fails when a set's texture or function stays a call. The set of
an `Array` of a structure had the structure's whole release in line for the
element it replaces (its fields' releases, its free), and LLVM kept that
texture out of line (unionfind's `l2r_array_set`). Each `put` sets: an
`Array` of a structure (at a proved index and with `set!`), `Array (Option
P)` (`none`, an immediate, replaced and replacing), `Array String`, `Array
(Array Nat)`, `Array Nat`, `Array Int`, `Array UInt64`, `ByteArray`,
`FloatArray`. A replaced element is sometimes the last reference (freed)
and sometimes shared (read first, or kept with the array), and every 997th
round the arrays are kept, so that the next sets copy them first. (At a call
site that LLVM judges cold, deep in branches, the set textures of every
element type stay calls: they are above the cold-site threshold.) -/

structure P where
  x : Nat
  y : Nat
deriving Inhabited

@[noinline] def putP (a : Array P) (i : Nat) (h : i < a.size) (n : Nat) : Array P :=
  if n % 4 = 0 then a else
  let p := a[i]'h
  let a := a.set i { p with x := p.x + n } h
  a.set! (i + 1) { x := n, y := if n % 19 = 0 then 2^64 + i else i }

@[noinline] def putO (a : Array (Option P)) (i : Nat) (h : i < a.size) (n : Nat) : Array (Option P) :=
  if n % 4 = 0 then a else
  a.set i (if n % 23 = 0 then none else some { x := n, y := i }) h

@[noinline] def putS (a : Array String) (b : Array (Array Nat)) (i : Nat) (n : Nat) :
    Array String × Array (Array Nat) :=
  if n % 4 = 0 then (a, b) else
  (a.set! i (toString n), b.set! i #[n, i])

@[noinline] def putN (a : Array Nat) (b : Array Int) (c : Array UInt64) (i : Nat) (n : Nat) :
    Array Nat × Array Int × Array UInt64 :=
  if n % 4 = 0 then (a, b, c) else
  (a.set! i (if n % 19 = 0 then 2^64 + n else n), b.set! i (Int.ofNat n - 2^40), c.set! i (n * 3).toUInt64)

@[noinline] def putB (a : ByteArray) (f : FloatArray) (i : Nat) (n : Nat) : ByteArray × FloatArray :=
  if n % 4 = 0 then (a, f) else
  (a.set! i n.toUInt8, f.set! i n.toFloat)

def main (args : List String) : IO Unit := do
  let n := args.length + 64
  let mut ap := (Array.range n).map fun i => ({ x := i, y := i * 2 } : P)
  let mut ao : Array (Option P) := (Array.range n).map fun i => if i % 3 = 0 then none else some { x := i, y := 1 }
  let mut as := (Array.range n).map toString
  let mut aa := (Array.range n).map fun i => #[i]
  let mut an := Array.range n
  let mut ai : Array Int := (Array.range n).map Int.ofNat
  let mut au := (Array.range n).map (·.toUInt64)
  let mut ab := ByteArray.mk ((Array.range n).map (·.toUInt8))
  let mut af : FloatArray := ⟨(Array.range n).map (·.toFloat)⟩
  let mut kept : Array (Array P × Array (Option P) × Array String) := #[]
  let mut keptN : Array (Array Nat × Array Int × ByteArray) := #[]
  for k in [0:200000] do
    let i := k % (n - 1)
    if k % 997 = 0 then
      kept := kept.push (ap, ao, as)
      keptN := keptN.push (an, ai, ab)
    if h : i < ap.size then ap := putP ap i h k
    if h : i < ao.size then ao := putO ao i h k
    (as, aa) := putS as aa i k
    (an, ai, au) := putN an ai au i k
    (ab, af) := putB ab af i k
  let sumP (a : Array P) := a.foldl (fun s p => s + p.x + p.y) 0
  let sumO (a : Array (Option P)) := a.foldl (fun s o => match o with | none => s + 1 | some p => s + p.x) 0
  IO.println s!"structures {sumP ap}, options {sumO ao}, strings {as.foldl (· + ·.length) 0}"
  IO.println s!"arrays {aa.foldl (fun s b => s + b.foldl (· + ·) 0) 0}, nats {an.foldl (· + ·) 0}, ints {ai.foldl (· + ·) 0}"
  IO.println s!"words {au.foldl (· + ·) 0}, bytes {ab.foldl (fun s b => s + b.toNat) 0}, floats {af.foldl (· + ·) 0}"
  IO.println s!"kept {kept.size}: {kept.foldl (fun s (p, o, t) => s + sumP p + sumO o + t.size) 0}, {keptN.foldl (fun s (a, b, c) => s + a.foldl (· + ·) 0 + b.size + c.size) 0}"
