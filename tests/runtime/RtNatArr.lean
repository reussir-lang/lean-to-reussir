/-! Runtime test: `Array Nat`/`Array Int` (one tagged word per element, one
allocation per array): literals (pushes onto a shared empty array with
capacity), pushes onto shared arrays, growth, appends (also of an array to
itself), set/swap/pop/extract/reverse/shrink on unique and shared arrays,
big elements (2^63, 2^64, negative and huge `Int`s) through every
operation, maps to and from other representations, nested arrays, sorting,
`Array.mkEmpty`/`ByteArray.emptyWithCapacity` with large capacities, and
in-bounds reads in loops (insertion sort, binary search). -/

def big : Array Nat := #[0, 1, 2^62, 2^63 - 1, 2^63, 2^64 - 1, 2^64, 2^70 + 3, 5]

@[noinline] def lit (i : Nat) : Array Nat := #[i, i + 1, 2^64 + i, i % 7]

def main (args : List String) : IO Unit := do
  let k := args.length
  -- literals: each a fresh array; the shared empty closed term stays empty
  let mut acc : Array (Array Nat) := #[]
  for i in [0:6] do
    acc := acc.push (lit (i + k))
  IO.println s!"lits {acc} {(lit k).size} {(#[] : Array Nat).size}"
  let l := lit (3 + k)
  let l2 := l.push 9          -- shared: copied
  let l3 := l.set! 0 100      -- shared: copied
  IO.println s!"shared {l} {l2} {l3}"
  -- growth with big elements interleaved
  let mut a : Array Nat := #[]
  for i in [0:300] do
    a := a.push (if i % 37 == 0 then 2^64 + i else i)
  IO.println s!"grow {a.size} {a[0]!} {a[37]!} {a[299]!} {a.foldl (· + ·) 0}"
  -- appends, also of an array to itself and of empty arrays
  let b := a ++ a
  let c := (#[] : Array Nat) ++ big ++ #[]
  IO.println s!"append {b.size} {b[300]!} {b[337]!} {c} {(big ++ big).size}"
  let mut d : Array Nat := #[]
  for i in [0:50] do
    d := d ++ #[i, 2^65 + i]
  IO.println s!"appendLit {d.size} {d[1]!} {d[99]!}"
  -- updates on unique and shared arrays
  let e := big.set! 2 7 |>.set! 7 (2^80) |>.swapIfInBounds 0 6
  IO.println s!"set {e} {big}"
  IO.println s!"pop {big.pop} {big.pop.pop.size} reverse {big.reverse} extract {big.extract 3 7} {big.extract 7 3}"
  IO.println s!"shrink {(big.extract 0 4)} {big.take 3} {big.drop 6} {(big.modify 6 (· + 1))}"
  IO.println s!"swapOob {big.swapIfInBounds 0 100} getOob {big[100]?} {big.getD 100 42}"
  -- maps between representations (boxed elements on the way)
  IO.println s!"maps {big.map (· % 2 == 0)} {big.map (fun x => (x, x % 7))} {big.map some} {big.map (·.toUInt64)}"
  IO.println s!"mapBack {(big.map (·.toUInt64)).map (·.toNat)} {(big.map toString).map String.length}"
  -- Int arrays
  let ints : Array Int := #[0, -1, 2^62, -(2^62), -(2^62) - 1, 2^63, -(2^63), -(2^64) - 7, 2^70]
  let ints2 := (ints.push (-5)).set! 1 (2^65) |>.reverse
  IO.println s!"ints {ints} {ints2} {ints.foldl (· + ·) 0} {ints.qsort (· < ·)}"
  -- nested and replicated
  let nested : Array (Array Nat) := Array.ofFn (n := 5) fun i => #[i.val, 2^64 * i.val, i.val % 3]
  IO.println s!"nested {nested} {(nested.map (·.size)).foldl (· + ·) 0} {Array.replicate 3 (2^64)} {Array.replicate 4 7}"
  -- sorting and searching: in-bounds reads in loops
  let r : Array Nat := (Array.range 200).map (fun i => (i * 7919 + k) % 211 + (if i % 50 == 0 then 2^64 else 0))
  let s1 := r.insertionSort (· < ·)
  let s2 := r.qsort (· < ·)
  IO.println s!"sort {s1 == s2} {s1.take 5} {s1[199]!} {(s2.binSearch (2^64) (· < ·)).isSome} {(s2.binSearch 1000 (· < ·)).isSome}"
  let u : Array UInt64 := (Array.range 200).map (fun i => ((i * 7919 + k) % 211).toUInt64)
  IO.println s!"sortU {(u.insertionSort (· < ·)).take 5} {(u.qsort (· < ·)).toList.drop 195}"
  -- capacities: honoured as natively
  let mut m : Array Nat := Array.mkEmpty (2^25)
  for i in [0:100] do
    m := m.push i
  let mut bytes := ByteArray.emptyWithCapacity (2^25 + 5)
  for i in [0:1000] do
    bytes := bytes.push i.toUInt8
  IO.println s!"capacity {m.size} {m[99]!} {bytes.size} {bytes[999]!}"
