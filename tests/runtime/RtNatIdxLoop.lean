/-! Runtime test: a loop-carried index after a proved access. After `a[i]`
with a proof (and `ByteArray.get`, `a.set i x h`, `a.swap i j`) lean2rr uses
the access's index word as a `Nat` in place of the index (`rebindIndex`,
Lower/Code), except in a loop-carried increment: `i + k` (`k` a literal)
passed to a self tail call at `i`'s own position reads the parameter `i`
itself (`loopCarriedAdds`). Pinned: self-recursive loops over arrays of 0,
1, 2, 7 and 1000 elements that increment one index, two indices (a
partition step), with the literal first (`1 + i`), by literals at and past
the immediates (2^60, 2^61 - 1, 2^61, 2^63, 2^64: the next index is a big
`Nat`, the loop then ends), with the increment also used elsewhere (in a
second read, in the result), passed at another position (not
loop-carried), in a call that is not a tail call, in a loop through an
inner join point, and loops entered with big indices (2^60, 2^61, 2^63,
2^64, 2^100: the access is never reached, the indices returned as they
came); and `Array.qsort`, whose partition loop increments both indices
after its reads and swaps. -/

@[noinline] def idx (n : Nat) : Nat := n

@[noinline] def mkArr (n seed : Nat) : Array Nat := Id.run do
  let mut a := Array.mkEmpty n
  let mut x := seed
  for _ in [:n] do
    a := a.push (x % 1000)
    x := (x * 1103515245 + 12345) % 2147483648
  return a

/-- One index, `+ 1` after the read. -/
@[noinline] def sumFrom (a : Array Nat) (i acc : Nat) : Nat :=
  if h : i < a.size then
    let v := a[i]
    if v == 1000 then acc else sumFrom a (i + 1) (acc + v)
  else acc + i
termination_by a.size - i

/-- The literal first: `1 + i`. -/
@[noinline] def sumFromL (a : Array Nat) (i acc : Nat) : Nat :=
  if h : i < a.size then
    let v := a[i]
    if v == 1000 then acc else sumFromL a (1 + i) (acc * 3 + v)
  else acc + i
termination_by a.size - i

/-- A step of 3 after each read; the index also in the accumulator. -/
@[noinline] def strideSum (a : Array Nat) (i acc : Nat) : Nat × Nat :=
  if h : i < a.size then
    let v := a[i]
    if v == 1000 then (acc, 0) else strideSum a (i + 3) (acc + v * (i + 1))
  else (acc, i)
termination_by a.size - i

/-- Steps at and past the immediates: after one read the next index is a
big `Nat` and the loop ends with it (`partial`: the termination proof
would compute with the literals). -/
@[noinline] partial def bigStep0 (a : Array Nat) (i acc : Nat) : Nat × Nat :=
  if h : i < a.size then
    let v := a[i]
    if v == 1000 then (acc, 0) else bigStep0 a (i + 1152921504606846976) (acc + v)
  else (acc, i)
@[noinline] partial def bigStep1 (a : Array Nat) (i acc : Nat) : Nat × Nat :=
  if h : i < a.size then
    let v := a[i]
    if v == 1000 then (acc, 0) else bigStep1 a (i + 2305843009213693951) (acc + v)
  else (acc, i)
@[noinline] partial def bigStep2 (a : Array Nat) (i acc : Nat) : Nat × Nat :=
  if h : i < a.size then
    let v := a[i]
    if v == 1000 then (acc, 0) else bigStep2 a (i + 2305843009213693952) (acc + v)
  else (acc, i)
@[noinline] partial def bigStep3 (a : Array Nat) (i acc : Nat) : Nat × Nat :=
  if h : i < a.size then
    let v := a[i]
    if v == 1000 then (acc, 0) else bigStep3 a (i + 9223372036854775808) (acc + v)
  else (acc, i)
@[noinline] partial def bigStep4 (a : Array Nat) (i acc : Nat) : Nat × Nat :=
  if h : i < a.size then
    let v := a[i]
    if v == 1000 then (acc, 0) else bigStep4 a (i + 18446744073709551616) (acc + v)
  else (acc, i)

/-- Two indices: a partition step that swaps at `i` and `j` and increments
both, or only `j`. -/
@[noinline] def partition (a : Array Nat) (pivot i j : Nat) (hi : i ≤ j) : Array Nat × Nat :=
  if hj : j < a.size then
    if a[j] < pivot then
      let a' := a.swap i j (by omega) hj
      partition a' pivot (i + 1) (j + 1) (by omega)
    else partition a pivot i (j + 1) (by omega)
  else (a, i)
termination_by a.size - j

/-- The increment used elsewhere too: in a second read and in the
accumulator. -/
@[noinline] def pairs (a : Array Nat) (i acc : Nat) : Nat :=
  if h : i < a.size then
    let v := a[i]
    if v == 1000 then acc else
    let j := i + 1
    let b := if h2 : j < a.size then a[j] else 0
    pairs a j (acc + v * b + j)
  else acc
termination_by a.size - i

/-- The increment passed at another position (the two indices exchanged:
not loop-carried). -/
@[noinline] def crossed (a : Array Nat) (i j acc fuel : Nat) : Nat :=
  match fuel with
  | 0 => acc + i * 1000 + j
  | fuel + 1 =>
    if h : i < a.size then
      let v := a[i]
      if v == 1000 then acc else crossed a (j + 1) (i + 1) (acc + v) fuel
    else acc + i * 1000 + j

/-- Not a tail call: the result of the recursive call is used. -/
@[noinline] def nonTail (a : Array Nat) (i : Nat) : Nat :=
  if h : i < a.size then
    let v := a[i]
    if v == 1000 then 0 else v + 2 * nonTail a (i + 1)
  else i
termination_by a.size - i

/-- A loop whose body branches through a join point before the tail
call; the read is in one branch only. -/
@[noinline] def jpLoop (a : Array Nat) (i acc : Nat) (flag : Bool) : Nat :=
  if h : i < a.size then
    let v := a[i]
    let acc' := if flag then acc + v else acc * 2 + v
    let acc'' := if v % 2 == 0 then acc' + 1 else acc' + 7
    jpLoop a (i + 1) acc'' (!flag)
  else acc + i
termination_by a.size - i

/-- `set` with a proof, then the index plus one. -/
@[noinline] def bump (a : Array Nat) (i : Nat) : Array Nat :=
  if h : i < a.size then bump (a.set i (a[i] + i)) (i + 1) else a
termination_by a.size - i

/-- `ByteArray.get` with a proof, `+ 2`. -/
@[noinline] def byteSum (b : ByteArray) (i acc : Nat) : Nat :=
  if h : i < b.size then
    let v := b[i]
    if v == 255 then acc else byteSum b (i + 2) (acc + v.toNat)
  else acc * 1000 + i
termination_by b.size - i

def main : IO Unit := do
  for n in [0, 1, 2, 7, 1000] do
    let a := mkArr (idx n) (n + 7)
    let (p, k) := partition a 500 0 0 (Nat.le_refl _)
    IO.println s!"{n}: sum {sumFrom a (idx 0) 0} {sumFrom a (idx 1) 5} sumL {sumFromL a (idx 0) 0 % 1000000007} stride {strideSum a (idx 0) 0} {strideSum a (idx 2) 1}"
    IO.println s!"  big {bigStep0 a (idx 0) 0} {bigStep1 a (idx 0) 0} {bigStep2 a (idx 0) 0} {bigStep3 a (idx 0) 0} {bigStep4 a (idx 0) 0} {bigStep4 a (idx 1) 0}"
    IO.println s!"  partition {k} {p.toList.take 12} {p.toList.foldl (· + ·) 0} pairs {pairs a (idx 0) 0} crossed {crossed a (idx 0) (idx 1) 0 (idx 50)}"
    IO.println s!"  nonTail {nonTail (a.extract 0 30) (idx 0) % 1000000007} jp {jpLoop a (idx 0) 0 true} bump {(bump a (idx 0)).toList.take 8} sorted {(a.qsort (· < ·)).toList.take 10}"
    IO.println s!"  bytes {byteSum (ByteArray.mk (a.map (·.toUInt8))) (idx 0) 0} {byteSum (ByteArray.mk (a.map (·.toUInt8))) (idx 1) 0}"
  -- Entered with big indices: no read, the index returned as it came.
  let a := mkArr 5 3
  for i in [2^60 - 1, 2^60, 2^61 - 1, 2^61, 2^62, 2^63 - 1, 2^63, 2^64, 2^100] do
    IO.println s!"from {i}: {sumFrom a (idx i) 1} {sumFromL a (idx i) 2} {strideSum a (idx i) 3} {bigStep2 a (idx i) 4} {(partition a 500 (idx i) (idx i) (Nat.le_refl _)).2} {pairs a (idx i) 5} {crossed a (idx i) (idx 0) 6 (idx 4)} {nonTail a (idx i)} {jpLoop a (idx i) 7 false} {byteSum (ByteArray.mk #[1, 2, 3]) (idx i) 8}"
