/-! Runtime test: loop states that are structures (optimization
`flatten-structs`). Each loop below keeps several variables in a structure
(`MProd`/`Prod` chains from `for`/`while`, a hand-written state, a range):
the pass splits such a parameter into its fields at their own types, and
rebuilds the structure only where it is used whole at the loop's exit. The
outputs must equal native's in every shape:
- a `for` loop in `IO` with six variables (the state rebuilt at the exit,
  inside `EST.Out.ok`);
- an Adler-32 fold over a `ByteArray` (`Nat × Nat`, `Id`);
- a `while` loop with an early `return`;
- an array updated in place inside the state (`dbgTraceIfShared` prints
  nothing: splitting keeps it unshared);
- an inner loop over short lists, run once per element of an outer loop,
  that passes its state on unchanged (no rebuild at its exit) or builds a
  new one;
- a state with a closure, a `Float`, a `UInt64`, a `Bool` and a proof;
- a stepped range (`Std.Legacy.Range`, passed on unchanged);
- a non-tail recursion whose structure argument is only read;
- `ptrEq` of a loop's result with its initial state (natively the same
  object when the loop ends at once, a new one otherwise). -/

@[noinline] def summary (n : Nat) : IO Nat := do
  let mut count := 0
  let mut sum := 0
  let mut last := 0
  let mut twins := 0
  let mut maxGap := 0
  let mut prev := 0
  for i in [0:n] do
    if i % 3 == 0 || i % 7 == 2 then
      count := count + 1
      sum := sum + i
      if prev > 0 then
        if i - prev == 2 then twins := twins + 1
        if i - prev > maxGap then maxGap := i - prev
      prev := i
      last := i
  IO.println s!"count={count} sum={sum} last={last} twins={twins} maxGap={maxGap}"
  return count

def adlerStep (s : Nat × Nat) (b : UInt8) : Nat × Nat :=
  let a := (s.1 + b.toNat) % 65521
  (a, (s.2 + a) % 65521)

@[noinline] def adler32 (data : ByteArray) : UInt32 :=
  let (a, b) := data.data.foldl adlerStep (1, 0)
  UInt32.ofNat (b * 65536 + a)

@[noinline] def firstSquareAbove (k : Nat) : Nat := Id.run do
  let mut d := 1
  let mut steps := 0
  while true do
    if d * d > k then return d * 1000 + steps
    d := d + 1
    steps := steps + 1
  return 0

@[noinline] def fillSquares (n : Nat) : Array Nat × Nat := Id.run do
  let mut arr := Array.replicate n 0
  let mut total := 0
  for i in [0:n] do
    let a := dbgTraceIfShared "arr shared" arr
    arr := a.set! i (i * i)
    total := total + i
  return (arr, total)

structure Best where
  key : Nat
  score : Nat
  hits : Nat

/-- The best entry of one short bucket: unchanged when no entry beats it. -/
@[noinline] def scanBucket : List (Nat × Nat) → Best → Best
  | [], b => b
  | (k, s) :: rest, b =>
    if s > b.score then scanBucket rest { key := k, score := s, hits := b.hits + 1 }
    else scanBucket rest b

@[noinline] def scanAll (buckets : Array (List (Nat × Nat))) : Best := Id.run do
  let mut best : Best := { key := 0, score := 0, hits := 0 }
  for bucket in buckets do
    best := scanBucket bucket best
  return best

structure Mixed where
  f : Nat → Nat
  x : Float
  w : UInt64
  flag : Bool
  n : Nat
  ok : n ≥ 0

@[noinline] def mixLoop (k : Nat) : String := Id.run do
  let mut m : Mixed := { f := (· + 1), x := 0.5, w := 1, flag := false, n := 0, ok := Nat.zero_le _ }
  for i in [0:k] do
    m := { f := fun y => m.f y + i, x := m.x * 1.5, w := m.w * 3 + UInt64.ofNat i, flag := !m.flag,
           n := m.n + 1, ok := Nat.zero_le _ }
  return s!"f 10 = {m.f 10} x = {m.x} w = {m.w} flag = {m.flag} n = {m.n}"

@[noinline] def stepped (n step : Nat) (h : 0 < step) : Nat × Nat := Id.run do
  let mut s := 0
  let mut c := 0
  for j in ({ start := 3, stop := n, step := step, step_pos := h } : Std.Legacy.Range) do
    s := s + j
    c := c + 1
  return (s, c)

inductive Tree where
  | leaf
  | node (l : Tree) (v : Nat) (r : Tree)

def mkTree : Nat → Tree
  | 0 => .leaf
  | d + 1 => .node (mkTree d) d (mkTree d)

/-- The weights are read, never stored: the argument is split without a
rebuild, also in a recursion that is not a tail call. -/
@[noinline] def weigh : Tree → Nat × Nat → Nat
  | .leaf, w => w.1
  | .node l v r, w => weigh l (w.1 + v, w.2) + weigh r (w.2, w.1 * 2 % 1000) + v

@[noinline] def countUp (s : Nat × Nat) (k : Nat) : Nat × Nat := Id.run do
  let mut s := s
  for _ in [0:k] do
    s := (s.1 + 1, s.2 + 2)
  return s

unsafe def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 20000
  let c ← summary n
  IO.println s!"summary count {c}"
  let bytes := ByteArray.mk ((List.range n).toArray.map fun i => UInt8.ofNat (i * 7 + 3))
  IO.println s!"adler32 {adler32 bytes}"
  IO.println s!"firstSquareAbove {firstSquareAbove n}"
  let (arr, total) := fillSquares (n / 10)
  IO.println s!"fill {arr.size} {arr.foldl (· + ·) 0} {total}"
  let buckets := (List.range (n / 4)).toArray.map fun i =>
    if i % 3 == 0 then [] else if i % 3 == 1 then [(i, i * 37 % 101)] else [(i, i % 17), (i + 1, i * 13 % 89)]
  let b := scanAll buckets
  IO.println s!"best key={b.key} score={b.score} hits={b.hits}"
  IO.println (mixLoop 25)
  IO.println s!"stepped {stepped n 7 (by decide)}"
  IO.println s!"weigh {weigh (mkTree 12) (1, 2)}"
  let s0 : Nat × Nat := (n, n + 1)
  let s1 := countUp s0 0
  let s2 := countUp s0 3
  IO.println s!"countUp {s1} {s2} same0={ptrEq s0 s1} same3={ptrEq s0 s2}"
