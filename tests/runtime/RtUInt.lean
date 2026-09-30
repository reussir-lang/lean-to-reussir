/-! Runtime test: `UInt8/16/32/64`, `USize` and `Int8/16/32/64`, `ISize`:
wrapping, division by zero, shifts by at least the width, conversions,
`log2`, float saturation, `toString`. -/

def u8s (k : Nat) : List UInt8 := [0, 1, 2, 7, 127, 128, 200, 254, 255, k.toUInt8]
def u16s (k : Nat) : List UInt16 := [0, 1, 255, 256, 32767, 32768, 65534, 65535, k.toUInt16]
def u32s (k : Nat) : List UInt32 := [0, 1, 65535, 65536, 2147483647, 2147483648, 4294967294, 4294967295, k.toUInt32]
def u64s (k : Nat) : List UInt64 := [0, 1, 4294967295, 4294967296, 9223372036854775807, 9223372036854775808,
  18446744073709551614, 18446744073709551615, k.toUInt64]
def i8s (k : Nat) : List Int8 := [0, 1, -1, 2, -2, 7, 127, -128, -127, 100, k.toInt8]
def i16s (k : Nat) : List Int16 := [0, 1, -1, 32767, -32768, -32767, 300, -300, k.toInt16]
def i32s (k : Nat) : List Int32 := [0, 1, -1, 2147483647, -2147483648, -2147483647, 100000, -100000, k.toInt32]
def i64s (k : Nat) : List Int64 := [0, 1, -1, 9223372036854775807, -9223372036854775808, -9223372036854775807,
  4294967296, -4294967296, k.toInt64]

def floats : List Float := [0.0, -0.0, 0.5, -0.5, 1.5, -1.5, 127.9, 128.0, -128.9, -129.0, 255.9, 256.0,
  65535.5, 65536.0, 2147483647.5, -2147483648.5, 4294967295.9, 4294967296.0,
  9223372036854775807.0, -9223372036854775808.0, 1.8446744073709552e19, 1e300, -1e300,
  1.0/0.0, -1.0/0.0, 0.0/0.0]

def main (args : List String) : IO Unit := do
  let k := args.length + 3
  for a in u8s k do
    for b in u8s k do
      IO.println s!"u8 {a} {b}: {a+b} {a-b} {a*b} {a/b} {a%b} {a &&& b} {a ||| b} {a ^^^ b} {a <<< b} {a >>> b} {decide (a < b)} {decide (a ≤ b)} {a == b}"
    IO.println s!"u8 {a}: ~ {~~~a} neg {-a} log2 {a.log2} toNat {a.toNat} {a.toUInt16} {a.toUInt32} {a.toUInt64} {a.toUSize} {a.toFloat} {a.toInt8} {Char.ofNat a.toNat}"
  for a in u16s k do
    for b in u16s k do
      IO.println s!"u16 {a} {b}: {a+b} {a-b} {a*b} {a/b} {a%b} {a &&& b} {a ||| b} {a ^^^ b} {a <<< b} {a >>> b} {decide (a < b)}"
    IO.println s!"u16 {a}: ~ {~~~a} neg {-a} log2 {a.log2} {a.toUInt8} {a.toUInt32} {a.toUInt64} {a.toFloat} {a.toInt16}"
  for a in u32s k do
    for b in u32s k do
      IO.println s!"u32 {a} {b}: {a+b} {a-b} {a*b} {a/b} {a%b} {a &&& b} {a ||| b} {a ^^^ b} {a <<< b} {a >>> b} {decide (a < b)}"
    IO.println s!"u32 {a}: ~ {~~~a} neg {-a} log2 {a.log2} {a.toUInt8} {a.toUInt16} {a.toUInt64} {a.toUSize} {a.toFloat} {a.toInt32}"
  for a in u64s k do
    for b in u64s k do
      IO.println s!"u64 {a} {b}: {a+b} {a-b} {a*b} {a/b} {a%b} {a &&& b} {a ||| b} {a ^^^ b} {a <<< b} {a >>> b} {decide (a < b)}"
    IO.println s!"u64 {a}: ~ {~~~a} neg {-a} log2 {a.log2} {a.toUInt8} {a.toUInt16} {a.toUInt32} {a.toUSize} {a.toFloat} {a.toInt64} {a.toNat}"
    let s := a.toUSize
    IO.println s!"usize {s}: {s + 1} {s * 3} {s / 0} {s % 0} {s <<< 65} {s >>> 64} {s.log2} {s.toUInt32} {s.toUInt64} {s.toNat} {s.toFloat}"
  for a in i8s k do
    for b in i8s k do
      IO.println s!"i8 {a} {b}: {a+b} {a-b} {a*b} {a/b} {a%b} {a &&& b} {a ||| b} {a ^^^ b} {a <<< b} {a >>> b} {decide (a < b)} {decide (a ≤ b)} {a == b}"
    IO.println s!"i8 {a}: ~ {~~~a} neg {-a} abs {a.abs} toInt {a.toInt} toNat {a.toNatClampNeg} {a.toInt16} {a.toInt32} {a.toInt64} {a.toISize} {a.toFloat} {a.toUInt8}"
  for a in i16s k do
    for b in i16s k do
      IO.println s!"i16 {a} {b}: {a+b} {a-b} {a*b} {a/b} {a%b} {a <<< b} {a >>> b} {decide (a < b)}"
    IO.println s!"i16 {a}: ~ {~~~a} neg {-a} {a.toInt} {a.toInt8} {a.toInt32} {a.toInt64} {a.toFloat}"
  for a in i32s k do
    for b in i32s k do
      IO.println s!"i32 {a} {b}: {a+b} {a-b} {a*b} {a/b} {a%b} {a <<< b} {a >>> b} {decide (a < b)}"
    IO.println s!"i32 {a}: ~ {~~~a} neg {-a} {a.toInt} {a.toInt8} {a.toInt16} {a.toInt64} {a.toFloat}"
  for a in i64s k do
    for b in i64s k do
      IO.println s!"i64 {a} {b}: {a+b} {a-b} {a*b} {a/b} {a%b} {a <<< b} {a >>> b} {decide (a < b)}"
    IO.println s!"i64 {a}: ~ {~~~a} neg {-a} {a.toInt} {a.toInt8} {a.toInt16} {a.toInt32} {a.toISize} {a.toFloat}"
    let s := a.toISize
    IO.println s!"isize {s}: {s + 1} {s * 3} {s / -1} {s % -1} {s / 0} {s % 0} {s >>> 63} {s.toInt} {s.toInt64}"
  for f in floats do
    IO.println s!"float {f}: {f.toUInt8} {f.toUInt16} {f.toUInt32} {f.toUInt64} {f.toUSize} {f.toInt8} {f.toInt16} {f.toInt32} {f.toInt64} {f.toISize}"
    let g := f.toFloat32
    IO.println s!"float32 {g}: {g.toUInt8} {g.toUInt16} {g.toUInt32} {g.toUInt64} {g.toInt8} {g.toInt16} {g.toInt32} {g.toInt64}"
  for n in [0, 255, 256, 65536, 4294967296, 18446744073709551615, 18446744073709551616, 340282366920938463463374607431768211457] do
    IO.println s!"ofNat {n}: {UInt8.ofNat n} {UInt16.ofNat n} {UInt32.ofNat n} {UInt64.ofNat n} {USize.ofNat n} {Int8.ofNat n} {Int16.ofNat n} {Int32.ofNat n} {Int64.ofNat n}"
  for i in [(0 : Int), -1, -128, -129, 2147483648, -9223372036854775809, -18446744073709551617, 340282366920938463463374607431768211457] do
    IO.println s!"ofInt {i}: {Int8.ofInt i} {Int16.ofInt i} {Int32.ofInt i} {Int64.ofInt i} {ISize.ofInt i}"
  IO.println s!"bool {true.toUInt8} {false.toUInt64} {true.toInt8} {(true : Bool).toUInt32}"
  IO.println s!"hash {hash (5 : UInt64)} {mixHash 1 2} {mixHash 18446744073709551615 12345} {hash (7 : UInt8)}"
