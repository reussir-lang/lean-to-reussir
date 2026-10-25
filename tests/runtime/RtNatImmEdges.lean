/-! Runtime test: `Nat` and `Int` at the edges of the immediates of both of
lean2rr's representations: Lean's (a `Nat` below 2^63, an `Int` in the
`int32` range) and Reussir's built-in integers under `--int-backend rcgmp`
(rcgmp's immediates: [-2^61, 2^61)). Each edge value is built three ways:
as a literal (under rcgmp a value outside the immediates is a read-only
object of the program's data), computed at run time, and read back from a
box (a `List`, an `Option`, an `Array` of boxes, a polymorphic function):
every operation and conversion, equality and order of all pairs (a literal
against a computed value of the same number), and the round trips. -/

def p (e k : Nat) : Nat := 2 ^ (e + k % 1)

/-- The edges as literals. -/
def natLits : List Nat :=
  [0, 1, 2147483647, 2147483648, 4294967295, 4294967296,
   2305843009213693951, 2305843009213693952, 2305843009213693953,
   4611686018427387903, 4611686018427387904, 4611686018427387905,
   9223372036854775807, 9223372036854775808, 9223372036854775809,
   18446744073709551615, 18446744073709551616, 18446744073709551617]

/-- The same edges, computed. -/
def natRun (k : Nat) : List Nat :=
  [0 + k, 1 + k, p 31 k - 1, p 31 k, p 32 k - 1, p 32 k,
   p 61 k - 1, p 61 k, p 61 k + 1,
   p 62 k - 1, p 62 k, p 62 k + 1,
   p 63 k - 1, p 63 k, p 63 k + 1,
   p 64 k - 1, p 64 k, p 64 k + 1]

def intLits : List Int :=
  [0, -1, 2147483647, 2147483648, -2147483648, -2147483649,
   2305843009213693951, 2305843009213693952, -2305843009213693952, -2305843009213693953,
   9223372036854775807, 9223372036854775808, -9223372036854775808, -9223372036854775809]

def intRun (k : Nat) : List Int :=
  let q (e : Nat) : Int := (p e k : Int)
  [(k : Int), (k : Int) - 1, q 31 - 1, q 31, -q 31, -q 31 - 1,
   q 61 - 1, q 61, -q 61, -q 61 - 1,
   q 63 - 1, q 63, -q 63, -q 63 - 1]

@[noinline] def viaBox {α : Type} (x : α) : α := x

def natOne (a : Nat) : String :=
  s!"{a}: succ {a + 1} pred {a - 1} *2 {a * 2} /3 {a / 3} %7 {a % 7} log2 {Nat.log2 a} " ++
  s!">>>1 {a >>> 1} <<<1 {a <<< 1} &&&mask {a &&& 0xFFFFFFFF} %2^61 {a % 2305843009213693952} " ++
  s!"%2^62 {a % 4611686018427387904} %2^64 {a % 18446744073709551616} u64 {a.toUInt64} " ++
  s!"usize {a.toUSize} u32 {a.toUInt32} i64 {a.toInt64} int {(a : Int)} neg {-(a : Int)} " ++
  s!"negSucc {Int.negSucc a} float {a.toFloat} ^2 {a ^ 2}"

def intOne (a : Int) : String :=
  s!"{a}: +1 {a + 1} -1 {a - 1} *-2 {a * -2} /3 {a / 3} %7 {a % 7} tdiv3 {a.tdiv 3} tmod7 {a.tmod 7} " ++
  s!"fdiv3 {a.fdiv 3} fmod7 {a.fmod 7} natAbs {a.natAbs} toNat {a.toNat} neg {-a} i64 {a.toInt64} " ++
  s!"i32 {a.toInt32} >>>1 {a >>> 1} float {Float.ofInt a}"

def main (args : List String) : IO Unit := do
  let k := args.length
  let ls := natLits
  let rs := natRun k
  for (a, b) in ls.zip rs do
    IO.println s!"lit {a} run {b}: == {a == b} < {decide (a < b)} <= {decide (a ≤ b)} cmp {repr (compare a b)}"
    IO.println (natOne a)
    IO.println (natOne b)
  -- Every pair, a literal against a computed value.
  let mut eqs := 0
  let mut lts := 0
  for a in ls do
    for b in rs do
      if a == b then eqs := eqs + 1
      if a < b then lts := lts + 1
      IO.println s!"{a} {b}: + {a + b} - {a - b} * {a * b} / {a / b} % {a % b} gcd {Nat.gcd a b} &&& {a &&& b} ^^^ {a ^^^ b}"
  IO.println s!"nat pairs: equal {eqs} less {lts}"
  -- Round trips through boxes.
  let boxed : List Nat := ls ++ rs
  let arr : Array Nat := boxed.toArray
  let opts : List (Option Nat) := boxed.map some
  for i in [0:arr.size] do
    let a := arr[i]!
    let b := viaBox a
    let c := (opts[i]!).getD 0
    IO.println s!"box {a}: {b} {c} {a == b && b == c} {(viaBox (a, a + 1)).2}"
  IO.println s!"sum {arr.foldl (· + ·) 0} max {arr.foldl max 0} sorted {(arr.qsort (· < ·)).toList == (arr.qsort (· < ·)).toList}"
  let il := intLits
  let ir := intRun k
  for (a, b) in il.zip ir do
    IO.println s!"lit {a} run {b}: == {a == b} < {decide (a < b)} <= {decide (a ≤ b)}"
    IO.println (intOne a)
    IO.println (intOne b)
  for a in il do
    for b in ir do
      IO.println s!"{a} {b}: + {a + b} - {a - b} * {a * b} / {a / b} % {a % b} == {a == b} < {decide (a < b)}"
  let iboxed : Array Int := (il ++ ir).toArray
  for i in [0:iboxed.size] do
    let a := iboxed[i]!
    IO.println s!"ibox {a}: {viaBox a} {(some a).getD 0} {viaBox a == a}"
