/-! Runtime test: fixed-width integer sweep. `UInt8/16/32/64` and `USize`:
`ofNat`/`toUIntN` of values up to 2^100, every pair of edge values through
`+ - * / % << >> &&& ||| ^^^` and comparisons (divisor 0, shifts at and past
the width), `~~~`, negation, `log2`, every width conversion, `toFloat`,
`toFloat32`, `ofNatClamp`, `isValidChar`, `hash`, `repr`. `Int8/16/32/64` and
`ISize`: `ofInt`/`ofNat` of ±2^63, ±2^64, 2^100, every pair (MIN / -1, MIN % -1,
arithmetic `>>>`, shifts by negative amounts), `abs`, `toNatClampNeg`,
sign-extending conversions, `toBitVec`, min/max values, `repr`/`reprPrec`/
`reprArg` of negatives, `hash`.
From the round-6 adversarial reviewers, area numbers (adv6/numbers), checks
UOps and SOps. -/

namespace UOps
-- from adv6/numbers/UOps.lean
-- Unsigned fixed-width integers: wrap, div/mod 0, shifts >= width, conversions.
@[noinline] def bn (n : Nat) : Nat := n
@[noinline] def b8 (n : UInt8) : UInt8 := n
@[noinline] def b16 (n : UInt16) : UInt16 := n
@[noinline] def b32 (n : UInt32) : UInt32 := n
@[noinline] def b64 (n : UInt64) : UInt64 := n
@[noinline] def bus (n : USize) : USize := n

def natVals : List Nat := [0, 1, 127, 128, 255, 256, 257, 65535, 65536, 2^31, 2^32 - 1, 2^32, 2^63, 2^64 - 1, 2^64, 2^64 + 5, 2^100 + 7, 3^50]

def main : IO Unit := do
  for n in natVals do
    let n := bn n
    IO.println s!"ofNat {n}: u8 {n.toUInt8} u16 {n.toUInt16} u32 {n.toUInt32} u64 {n.toUInt64} usize {n.toUSize} | {UInt8.ofNat n} {UInt16.ofNat n} {UInt32.ofNat n} {UInt64.ofNat n} {USize.ofNat n} | back {n.toUInt64.toNat} {n.toUSize.toNat} {n.toUInt8.toNat}"
  let us8 : List UInt8 := [0, 1, 2, 7, 8, 9, 127, 128, 200, 255]
  for a in us8 do
    for b in us8 do
      let a := b8 a; let b := b8 b
      IO.println s!"u8 {a} {b}: + {a+b} - {a-b} * {a*b} / {a/b} % {a%b} << {a <<< b} >> {a >>> b} & {a &&& b} | {a ||| b} ^ {a ^^^ b} < {decide (a < b)} <= {decide (a ≤ b)} == {a == b}"
    IO.println s!"u8 {a}: ~ {~~~(b8 a)} neg {-(b8 a)} log2 {(b8 a).log2} toU16 {(b8 a).toUInt16} toU32 {(b8 a).toUInt32} toU64 {(b8 a).toUInt64} toF {(b8 a).toFloat} toI8 {(b8 a).toInt8} toChar {repr (Char.ofNat (b8 a).toNat)}"
  let us16 : List UInt16 := [0, 1, 15, 16, 17, 255, 256, 32767, 32768, 65535]
  for a in us16 do
    for b in us16 do
      let a := b16 a; let b := b16 b
      IO.println s!"u16 {a} {b}: + {a+b} - {a-b} * {a*b} / {a/b} % {a%b} << {a <<< b} >> {a >>> b} < {decide (a < b)}"
    IO.println s!"u16 {a}: ~ {~~~(b16 a)} neg {-(b16 a)} log2 {(b16 a).log2} toU8 {(b16 a).toUInt8} toU32 {(b16 a).toUInt32} toI16 {(b16 a).toInt16}"
  let us32 : List UInt32 := [0, 1, 31, 32, 33, 65536, 2147483647, 2147483648, 4294967295]
  for a in us32 do
    for b in us32 do
      let a := b32 a; let b := b32 b
      IO.println s!"u32 {a} {b}: + {a+b} - {a-b} * {a*b} / {a/b} % {a%b} << {a <<< b} >> {a >>> b} < {decide (a < b)}"
    IO.println s!"u32 {a}: ~ {~~~(b32 a)} neg {-(b32 a)} log2 {(b32 a).log2} toU8 {(b32 a).toUInt8} toU16 {(b32 a).toUInt16} toU64 {(b32 a).toUInt64} toF {(b32 a).toFloat} toF32 {(b32 a).toFloat32} toI32 {(b32 a).toInt32} isValidChar {decide (b32 a).isValidChar}"
  let us64 : List UInt64 := [0, 1, 63, 64, 65, 4294967296, 9223372036854775807, 9223372036854775808, 18446744073709551615, 12345678901234567890]
  for a in us64 do
    for b in us64 do
      let a := b64 a; let b := b64 b
      IO.println s!"u64 {a} {b}: + {a+b} - {a-b} * {a*b} / {a/b} % {a%b} << {a <<< b} >> {a >>> b} < {decide (a < b)} xor {a ^^^ b}"
    IO.println s!"u64 {a}: ~ {~~~(b64 a)} neg {-(b64 a)} log2 {(b64 a).log2} toU8 {(b64 a).toUInt8} toU16 {(b64 a).toUInt16} toU32 {(b64 a).toUInt32} toUSize {(b64 a).toUSize} toF {(b64 a).toFloat} toF32 {(b64 a).toFloat32} toI64 {(b64 a).toInt64} toNat {(b64 a).toNat}"
  let uss : List USize := [0, 1, 63, 64, 65, 18446744073709551615, 9223372036854775808]
  for a in uss do
    for b in uss do
      let a := bus a; let b := bus b
      IO.println s!"usize {a} {b}: + {a+b} - {a-b} * {a*b} / {a/b} % {a%b} << {a <<< b} >> {a >>> b} < {decide (a < b)}"
    IO.println s!"usize {a}: ~ {~~~(bus a)} log2 {(bus a).log2} toU32 {(bus a).toUInt32} toU64 {(bus a).toUInt64} toNat {(bus a).toNat} toISize {(bus a).toISize}"
  IO.println s!"size {USize.size} {System.Platform.numBits}"
  IO.println s!"hash {hash (b64 12345)} {hash (b8 3)} {hash (b32 7)} {hash (bus 9)}"
  IO.println s!"ofNatLT/trunc: {UInt8.ofNatClamp (bn 300)} {UInt16.ofNatClamp (bn 70000)} {UInt32.ofNatClamp (bn (2^40))} {UInt64.ofNatClamp (bn (2^70))} {UInt8.ofNatClamp (bn 5)}"
  IO.println s!"repr: {repr (b8 200)} {repr (b64 18446744073709551615)} {(b32 255).toNat.toDigits 16} {String.ofList ((b64 18446744073709551615).toNat.toDigits 16)}"
end UOps

namespace SOps
-- from adv6/numbers/SOps.lean
-- Signed fixed-width integers: overflow, MIN/-1, shifts, sign extension, conversions.
@[noinline] def bn (n : Nat) : Nat := n
@[noinline] def bi (n : Int) : Int := n
@[noinline] def s8 (n : Int8) : Int8 := n
@[noinline] def s16 (n : Int16) : Int16 := n
@[noinline] def s32 (n : Int32) : Int32 := n
@[noinline] def s64 (n : Int64) : Int64 := n
@[noinline] def sis (n : ISize) : ISize := n

def intVals : List Int := [0, 1, -1, 127, 128, -128, -129, 255, 256, 32767, 32768, -32768, -32769, 2^31 - 1, 2^31, -2^31, -2^31 - 1, 2^63 - 1, 2^63, -2^63, -2^63 - 1, 2^64, -(2^64), 2^64 + 5, -(2^100) - 7, 2^100 + 7]

def main : IO Unit := do
  for n in intVals do
    let n := bi n
    IO.println s!"ofInt {n}: i8 {n.toInt8} i16 {n.toInt16} i32 {n.toInt32} i64 {n.toInt64} isize {n.toISize} | {Int8.ofInt n} {Int16.ofInt n} {Int32.ofInt n} {Int64.ofInt n} {ISize.ofInt n} | back {n.toInt64.toInt} {n.toInt8.toInt} {n.toInt32.toInt}"
  for n in [0, 127, 128, 255, 256, 2^63, 2^64 - 1, 2^64 + 1, 2^100] do
    let n := bn n
    IO.println s!"ofNat {n}: {Int8.ofNat n} {Int16.ofNat n} {Int32.ofNat n} {Int64.ofNat n} {ISize.ofNat n}"
  let v8 : List Int8 := [0, 1, -1, 7, 8, -8, 9, 127, -128, -127, 100]
  for a in v8 do
    for b in v8 do
      let a := s8 a; let b := s8 b
      IO.println s!"i8 {a} {b}: + {a+b} - {a-b} * {a*b} / {a/b} % {a%b} << {a <<< b} >> {a >>> b} & {a &&& b} | {a ||| b} ^ {a ^^^ b} < {decide (a < b)} <= {decide (a ≤ b)} == {a == b} cmp {repr (compare a b)} max {max a b}"
    let a := s8 a
    IO.println s!"i8 {a}: ~ {~~~a} neg {-a} abs {a.abs} toInt {a.toInt} toNat {a.toNatClampNeg} toI16 {a.toInt16} toI32 {a.toInt32} toI64 {a.toInt64} toIS {a.toISize} toU8 {a.toUInt8} toF {a.toFloat} toF32 {a.toFloat32} toBV {a.toBitVec}"
  let v16 : List Int16 := [0, 1, -1, 15, 16, 17, -16, 32767, -32768, 255, -256]
  for a in v16 do
    for b in v16 do
      let a := s16 a; let b := s16 b
      IO.println s!"i16 {a} {b}: + {a+b} - {a-b} * {a*b} / {a/b} % {a%b} << {a <<< b} >> {a >>> b} < {decide (a < b)}"
    let a := s16 a
    IO.println s!"i16 {a}: ~ {~~~a} neg {-a} abs {a.abs} toInt {a.toInt} toI8 {a.toInt8} toI32 {a.toInt32} toI64 {a.toInt64} toU16 {a.toUInt16} toNat {a.toNatClampNeg}"
  let v32 : List Int32 := [0, 1, -1, 31, 32, 33, -32, 2147483647, -2147483648, 65536, -65536]
  for a in v32 do
    for b in v32 do
      let a := s32 a; let b := s32 b
      IO.println s!"i32 {a} {b}: + {a+b} - {a-b} * {a*b} / {a/b} % {a%b} << {a <<< b} >> {a >>> b} < {decide (a < b)}"
    let a := s32 a
    IO.println s!"i32 {a}: ~ {~~~a} neg {-a} abs {a.abs} toInt {a.toInt} toI8 {a.toInt8} toI16 {a.toInt16} toI64 {a.toInt64} toU32 {a.toUInt32} toF {a.toFloat} toF32 {a.toFloat32}"
  let v64 : List Int64 := [0, 1, -1, 63, 64, 65, -64, 9223372036854775807, -9223372036854775808, 4294967296, -4294967296, 3037000500]
  for a in v64 do
    for b in v64 do
      let a := s64 a; let b := s64 b
      IO.println s!"i64 {a} {b}: + {a+b} - {a-b} * {a*b} / {a/b} % {a%b} << {a <<< b} >> {a >>> b} < {decide (a < b)}"
    let a := s64 a
    IO.println s!"i64 {a}: ~ {~~~a} neg {-a} abs {a.abs} toInt {a.toInt} toI8 {a.toInt8} toI16 {a.toInt16} toI32 {a.toInt32} toIS {a.toISize} toU64 {a.toUInt64} toF {a.toFloat} toF32 {a.toFloat32} toNat {a.toNatClampNeg} toBV {a.toBitVec.toNat}"
  let vis : List ISize := [0, 1, -1, 63, 64, -64, 9223372036854775807, -9223372036854775808]
  for a in vis do
    for b in vis do
      let a := sis a; let b := sis b
      IO.println s!"isize {a} {b}: + {a+b} - {a-b} * {a*b} / {a/b} % {a%b} << {a <<< b} >> {a >>> b} < {decide (a < b)}"
    let a := sis a
    IO.println s!"isize {a}: ~ {~~~a} neg {-a} abs {a.abs} toInt {a.toInt} toI32 {a.toInt32} toI64 {a.toInt64} toUSize {a.toUSize} toNat {a.toNatClampNeg}"
  IO.println s!"minmax: {Int8.minValue} {Int8.maxValue} {Int16.minValue} {Int32.minValue} {Int64.minValue} {Int64.maxValue} {ISize.minValue} {ISize.maxValue}"
  IO.println s!"repr: {repr (s8 (-5))} {repr (s64 (-9223372036854775808))} {reprPrec (s32 (-3)) 70} {reprArg (s16 (-7))}"
  IO.println s!"hash: {hash (s8 (-1))} {hash (s64 (-1))} {hash (s32 (-2))}"
end SOps

def main : IO Unit := do
  IO.println "=== UOps"
  UOps.main
  IO.println "=== SOps"
  SOps.main
