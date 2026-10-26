/-! Runtime test: the index of an access that a proof keeps in range, used
again after the access: `a[i]` with a proof (`fget`), `ByteArray.get`,
`a.set i x h` (`fset`), `ByteArray.set`, `a.swap i j` (`fswap`), also
through `Vector` and `Array.qsort`. lean2rr
uses the access's index word as a `Nat` (`l2r_nat_of_index`) in place of
the index after the access (`rebindIndex`, Lower/Code). Pinned: loops up
to the size of arrays of 0, 1, 2, 7 and 1000 elements (after the last
access the index plus one is the size), `qsort` (its partition loop
swaps and reads at the indices it then increments), an insertion sort by
`swap`, a binary search, a search that returns its index, `set` and
`swap` at one index twice, `set` of the index at itself, a reversal by
`Vector.swap`, a shared array's `set` (a copy), and
arithmetic on the index after the access that leaves the immediates
(`i + 2^61`, `i * 2^64`, `i <<< 62`, `2^63 - i`, ...) or makes a big
index for `get!`, `get?`, `set!` and `swapIfInBounds` (near 2^61, 2^63
and 2^64: their panics and defaults). -/

@[noinline] def idx (n : Nat) : Nat := n

/-- The arrays of the qsort benchmark: `x₀ := seed`, `x * 1664525 + 1013904223`. -/
@[noinline] def mkArr (n seed : Nat) : Array UInt32 := Id.run do
  let mut a := Array.mkEmpty n
  let mut x : UInt32 := seed.toUInt32
  for _ in [:n] do
    a := a.push x
    x := x * 1664525 + 1013904223
  return a

/-- `fget` in a range loop, the index then in arithmetic. -/
@[noinline] def weighted (a : Array UInt32) : Nat := Id.run do
  let mut s := 0
  for h : i in [:a.size] do
    s := s + a[i].toNat * (i + 1) + i / 3
  return s

/-- Whether `a` is sorted: reads at `i` and `i + 1`. -/
@[noinline] def isSorted (a : Array UInt32) : Bool := Id.run do
  for h : i in [:a.size] do
    if h2 : i + 1 < a.size then
      if a[i + 1] < a[i] then return false
  return true

/-- The index of the first `p`, or the size. -/
@[noinline] def findIdx (a : Array UInt32) (p : UInt32) : Nat := Id.run do
  for h : i in [:a.size] do
    if a[i] == p then return i
  return a.size

/-- Binary search for `x` in a sorted array: the index of a match. -/
@[noinline] def bsearch (a : Array UInt32) (x : UInt32) : Option Nat := Id.run do
  let mut lo := 0
  let mut hi := a.size
  for _ in [:64] do
    if lo < hi then
      let mid := (lo + hi) / 2
      if h : mid < a.size then
        let v := a[mid]
        if v == x then return some mid
        if v < x then lo := mid + 1 else hi := mid
  return none

/-- Insertion sort by `swap` at `j` and `j - 1`, both read first. -/
@[noinline] def insertionSort (a : Array Nat) : Array Nat := Id.run do
  let mut a := a
  for i in [1:a.size] do
    let mut j := i
    for _ in [:i] do
      if h : 0 < j ∧ j < a.size then
        if a[j] < a[j - 1] then
          a := a.swap j (j - 1)
          j := j - 1
  return a

/-- `Vector.set` and reads in a loop: `v[i] * 3 + i`, then `i` again. -/
@[noinline] def vecStep {n : Nat} (v : Vector UInt32 n) : Vector UInt32 n × Nat := Id.run do
  let mut v := v
  let mut t := 0
  for h : i in [:n] do
    v := v.set i (v[i] * 3 + i.toUInt32)
    t := t + i * 2^64 + v[i].toNat
  return (v, t)

/-- `set` and `swap` at one index twice; the index after them. -/
@[noinline] def sameIdx (a : Array Nat) (i : Nat) (h : i < a.size) : Array Nat × Nat :=
  let b := a.swap i i
  let c := b.set i (i + 2^62) (by simp [b]; exact h)
  (c, i * 2^64 + i)

/-- `set` at `i` of the value `i` (`Array Nat`), then the index. -/
@[noinline] def setSelf (a : Array Nat) (i : Nat) (h : i < a.size) : Array Nat × Nat :=
  let b := a.set i i h
  (b, i + 1)

/-- `Vector.swap` at `i` and `n - 1 - i` in a loop (a reversal), both then
in arithmetic. -/
@[noinline] def vecReverse {n : Nat} (v : Vector Nat n) : Vector Nat n × Nat := Id.run do
  let mut v := v
  let mut t := 0
  for h : i in [:n / 2] do
    have hi : i < n / 2 := Membership.get_elem_helper h rfl
    v := v.swap i (n - 1 - i) (by omega) (by omega)
    t := t + i * 3 + (n - 1 - i) * 2^64
  return (v, t)

/-- A shared array's `set` (a copy), then the index. -/
@[noinline] def sharedSet (a : Array Nat) (i : Nat) (h : i < a.size) : Array Nat × Array Nat × Nat :=
  let b := a.set i 99 h
  (a, b, i + 2^61)

/-- `ByteArray.get` and `set` with proofs, then the index. -/
@[noinline] def bytesStep (b : ByteArray) (i : Nat) (h : i < b.size) : ByteArray × Nat :=
  let x := b[i]
  let c := b.set i (x + 1) h
  (c, i <<< 62 + x.toNat)

/-- Arithmetic on the index after the read, past the immediates. -/
@[noinline] def bigOps (a : Array Nat) : List Nat := Id.run do
  let mut out := []
  for h : i in [:a.size] do
    let x := a[i]
    out := (x + i + 2^61) :: (i * 2^64 + x) :: (i <<< 62) :: (2^63 - i) :: (i - 3) :: (i ^ 5) ::
      (i + 2^61 - 1) :: ((i + 2^64) % 7) :: (i &&& 6) :: out
  return out.reverse

/-- A big index made from the index after the read: `get!`, `get?`, `set!`
and `swapIfInBounds` at `i + k`. -/
@[noinline] def bigIdx (a : Array Nat) (k : Nat) : String := Id.run do
  let mut r := ""
  for h : i in [:a.size] do
    let x := a[i]
    let j := i + k
    r := r ++ s!"{x}:{a[j]!}:{a[j]?}:{(a.set! j 7)[i]!}:{(a.swapIfInBounds i j)[i]!}:{j} "
  return r

/-- `qsort`, then the median and the last element, as the benchmark. -/
@[noinline] def sortStats (n : Nat) : String :=
  let a := mkArr n (n + 1)
  let s := a.qsort (· < ·)
  s!"{n}: sorted {isSorted s} weighted {weighted s} median {s[s.size / 2]?} last {s[s.size - 1]?} find {findIdx s (s[s.size / 3]!)} bsearch {bsearch s (s[s.size / 3]!)}"

def main : IO Unit := do
  for n in [0, 1, 2, 3, 7, 100, 1000] do
    IO.println (sortStats (idx n))
  let a : Array Nat := #[5, 3, 9, 1, 7, 2, 8]
  IO.println s!"insertion {insertionSort a} {insertionSort #[]} {insertionSort #[4]}"
  let v : Vector UInt32 7 := Vector.ofFn fun i => (idx i.val).toUInt32 * 2654435761 + 12345
  let (v2, t) := vecStep v
  IO.println s!"vector {v2.toArray} {t}"
  let r5 : Vector Nat 5 := Vector.ofFn fun i => idx i.val * 10
  let r6 : Vector Nat 6 := Vector.ofFn fun i => idx i.val + 2^62
  let r1 : Vector Nat 1 := Vector.ofFn fun i => idx i.val
  IO.println s!"reverse {(vecReverse r5).1.toArray} {(vecReverse r5).2} {(vecReverse r6).1.toArray} {(vecReverse r6).2} {(vecReverse r1).1.toArray} {(vecReverse r1).2}"
  for i in [0, 3, 6] do
    if h : idx i < a.size then
      let (c, t) := sameIdx a (idx i) h
      let (a1, b1, t1) := sharedSet a (idx i) h
      IO.println s!"same {c} {t} shared {a1} {b1} {t1} self {setSelf a (idx i) h}"
  let bytes : ByteArray := ⟨#[1, 2, 255, 4]⟩
  for i in [0, 2, 3] do
    if h : idx i < bytes.size then
      let (c, t) := bytesStep bytes (idx i) h
      IO.println s!"bytes {c.toList} {t}"
  IO.println s!"bigOps {bigOps #[10, 20, 30]}"
  IO.println s!"bigOps0 {bigOps #[]}"
  for k in [0, 1, 2^61 - 2, 2^61 - 1, 2^61, 2^62, 2^63 - 2, 2^63 - 1, 2^63, 2^64 - 1, 2^64] do
    IO.println s!"bigIdx {k}: {bigIdx #[4, 6] (idx k)}"
