/-! Runtime test: `Nat` and `Int` at the boundaries of lean2rr's one-word
representation (Lean's: a `Nat` is a small value below 2^63, an `Int` in
the `int32` range; other values are big numbers), for every arithmetic,
bitwise, comparison and conversion extern on both sides of 2^62, 2^63 and
2^64, and for the fast paths' own limits (products of factors around
2^31 and 2^32, exponents, shift amounts). Values are built at runtime. -/

def p62 (k : Nat) : Nat := 2 ^ (62 + k % 1)
def p63 (k : Nat) : Nat := 2 ^ (63 + k % 1)
def p64 (k : Nat) : Nat := 2 ^ (64 + k % 1)

def edges (k : Nat) : List Nat :=
  [0, 1, 2, 3, 2147483647, 2147483648, 4294967295, 4294967296,
   3037000499, 3037000500, p62 k - 1, p62 k, p62 k + 1, p63 k - 2, p63 k - 1, p63 k, p63 k + 1,
   p64 k - 1, p64 k, p64 k + 1, p64 k * p64 k + 7]

def natOps (a b : Nat) : String :=
  s!"{a} {b}: + {a + b} - {a - b} {b - a} * {a * b} / {a / b} % {a % b} " ++
  s!"&&& {a &&& b} ||| {a ||| b} ^^^ {a ^^^ b} == {a == b} < {decide (a < b)} <= {decide (a ≤ b)} " ++
  s!"cmp {repr (compare a b)} gcd {Nat.gcd a b} max {max a b}"

def intEdges (k : Nat) : List Int :=
  let q : Int := (p62 k : Int)
  [0, 1, -1, 46340, 46341, -46341, 65536, -65536, 2147483646, 2147483647, -2147483647, -2147483648,
   2147483648, -2147483649, 3037000499, -3037000500,
   q - 1, q, q + 1, -q + 1, -q, -q - 1, 2 * q - 1, 2 * q, -2 * q, -2 * q - 1,
   (p64 k : Int), -(p64 k : Int), (p64 k : Int) * (p64 k : Int)]

def intOps (a b : Int) : String :=
  s!"{a} {b}: + {a + b} - {a - b} * {a * b} / {a / b} % {a % b} tdiv {a.tdiv b} tmod {a.tmod b} " ++
  s!"fdiv {a.fdiv b} fmod {a.fmod b} == {a == b} < {decide (a < b)} <= {decide (a ≤ b)} cmp {repr (compare a b)}"

def main (args : List String) : IO Unit := do
  let k := args.length
  let xs := edges k
  for a in xs do
    for b in xs do
      IO.println (natOps a b)
  for a in xs do
    IO.println s!"{a}: succ {a.succ} pred {a.pred} log2 {Nat.log2 a} repr {repr a} str {toString a} hash {hash a} sqrt {Nat.sqrt a}"
    IO.println s!"  u8 {a.toUInt8} u16 {a.toUInt16} u32 {a.toUInt32} u64 {a.toUInt64} usize {a.toUSize} i8 {a.toInt8} i64 {a.toInt64} isize {a.toISize}"
    IO.println s!"  float {a.toFloat} f32 {a.toFloat32} int {(a : Int)} neg {-(a : Int)} negSucc {Int.negSucc a} toNat {(a : Int).toNat}"
    IO.println s!"  u64rt {a.toUInt64.toNat} usizert {a.toUSize.toNat} u32rt {a.toUInt32.toNat} mixHash {mixHash (hash a) 7}"
    for s in [0, 1, 2, 30, 31, 32, 33, 61, 62, 63, 64, 65, 127] do
      IO.println s!"  <<< {s} {a <<< s} >>> {s} {a >>> s}"
    for e in [0, 1, 2, 3, 39, 40, 62, 63, 64] do
      if a < 4294967297 || e < 3 then
        IO.println s!"  ^ {e} {a ^ e}"
  -- powers at the fast path's limits
  for b in [2, 3, 7, 10, 2147483648, 3037000499] do
    for e in [1, 2, 19, 20, 38, 39, 40, 61, 62, 63, 64, 65] do
      if b < 100 || e < 4 then
        IO.println s!"{b} ^ {e} = {b ^ e}"
  -- unsigned to Nat at the top of the word
  for u in [(0 : UInt64), 9223372036854775807, 9223372036854775808, 18446744073709551615] do
    IO.println s!"UInt64 {u}: toNat {u.toNat} toNat+1 {u.toNat + 1} usize {u.toUSize.toNat} float {u.toFloat} back {(u.toNat).toUInt64}"
  for f in [0.0, 1.5, 9.2233720368547748e18, 9.2233720368547758e18, 1.8446744073709552e19, 3.0e30] do
    IO.println s!"Float {f}: toUInt64 {f.toUInt64} toNat {f.toUInt64.toNat} floor {f.floor} ofNat {Float.ofNat f.toUInt64.toNat}"
  let is := intEdges k
  for a in is do
    for b in is do
      IO.println (intOps a b)
  for a in is do
    IO.println s!"{a}: neg {-a} natAbs {a.natAbs} toNat {a.toNat} sign {a.sign} repr {repr a} hash {hash a} i64 {a.toInt64} i32 {a.toInt32} i8 {a.toInt8} isize {a.toISize}"
    IO.println s!"  >>> 1 {a >>> 1} >>> 62 {a >>> 62} >>> 63 {a >>> 63} ediv 2 {a / 2} emod 3 {a % 3} float {Float.ofInt a} pow2 {a ^ 2}"
  for n in [0, 1, (p62 k) - 2, (p62 k) - 1, p62 k, (p63 k) - 1, p63 k] do
    IO.println s!"negSucc {n} = {Int.negSucc n}; ofNat {n} = {Int.ofNat n}; -ofNat {-Int.ofNat n}"
  for i in [(0 : Int64), 4611686018427387903, 4611686018427387904, -4611686018427387904, -4611686018427387905, 9223372036854775807, -9223372036854775808] do
    IO.println s!"Int64 {i}: toInt {i.toInt} back {i.toInt.toInt64} plus1 {i.toInt + 1}"
  -- strings and arrays with positions/indices at and beyond the boundary
  let s := "héllo"
  for p in [0, 1, 6, p63 k - 1, p63 k, p64 k] do
    IO.println s!"pos {p}: get {(String.Pos.Raw.get s ⟨p⟩)} atEnd {String.Pos.Raw.atEnd s ⟨p⟩} next {(String.Pos.Raw.next s ⟨p⟩).byteIdx} extract {String.Pos.Raw.extract s 0 ⟨p⟩} valid {String.Pos.Raw.isValid s ⟨p⟩}"
  let arr : Array Nat := #[10, p63 k, 30]
  for i in [0, 1, 2, 3, p63 k, p64 k] do
    IO.println s!"arr[{i}]? {arr[i]?} set! {(arr.setIfInBounds i 99).toList} swap {(arr.swapIfInBounds 0 i).toList}"
