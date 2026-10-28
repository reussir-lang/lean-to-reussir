import Lean

/-!
The externs of Lean's library that are pure and total (`pureExterns`):
shared by unread-consts (Opt/UnreadConsts: a constant whose evaluation
calls only these cannot show) and by the erased-call merging of Stage 2
(`Mono.erasedMerges`: only these library externs are left out of the
aligned calls; every other one, such as `Array.get!Internal`, which can
panic, is aligned like a definition).
-/

namespace LeanToReussir
open Lean

/-- The operations of a fixed-width number type that are externs of Lean's
library and total: arithmetic wraps, a division or remainder by zero gives
0 or the dividend (`INT64_MIN / -1` too), a shift takes its amount modulo
the width, a conversion wraps or (from a float) saturates. -/
def fixedWidthOps : List String :=
  ["add", "sub", "mul", "div", "mod", "neg", "abs", "land", "lor", "xor", "complement",
   "shiftLeft", "shiftRight", "log2", "decEq", "decLt", "decLe", "ofNat", "ofNatLT", "ofInt",
   "ofBitVec", "toBitVec", "toNat", "toInt", "toUInt8", "toUInt16", "toUInt32", "toUInt64",
   "toUSize", "toInt8", "toInt16", "toInt32", "toInt64", "toISize", "toFloat", "toFloat32"]

/-- The float operations that are externs of Lean's library: IEEE 754
arithmetic and the C library's functions are total (a NaN or an infinity
for what has no number); a conversion to an integer saturates. -/
def floatOps : List String :=
  ["add", "sub", "mul", "div", "neg", "abs", "beq", "decLt", "decLe", "lt", "le", "isNaN",
   "isInf", "isFinite", "ofBits", "toBits", "ofModel", "toModel", "frExp", "scaleB", "toString",
   "sqrt", "cbrt", "exp", "exp2", "log", "log2", "log10", "pow", "sin", "cos", "tan", "asin",
   "acos", "atan", "atan2", "sinh", "cosh", "tanh", "asinh", "acosh", "atanh", "ceil", "floor",
   "round", "toFloat", "toFloat32", "toUInt8", "toUInt16", "toUInt32", "toUInt64", "toUSize",
   "toInt8", "toInt16", "toInt32", "toInt64", "toISize"]

/-- Externs of Lean's library that only compute their result from their
arguments: total (every argument has a result; see `fixedWidthOps` and
`floatOps`; an index with a proof that it is in bounds), with no message,
no closure argument and no runtime object (task, thunk, reference,
promise). The only way one can fail is to run out of a resource: memory,
or the exponent limit of `Nat.pow` and `Nat.shiftLeft` (natively an
internal panic above 2^32: the result would need more than 2^32 bits). An
extern that can panic (`Array.get!Internal`, `Array.set!`,
`ByteArray.get!`, `String.get!`, `sorryAx`), trace, read the outside world
or look at the representation of objects (`ptrAddrUnsafe`) is not listed.
A constructor with an extern implementation (`Array.mk`, `String.mk`,
`ByteArray.mk`) is a constructor (`classifyCall`). -/
def pureExterns : Std.HashSet Name := Id.run do
  let mut s : Std.HashSet Name := Std.HashSet.ofList [
    -- Nat and Int (big numbers).
    ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.div, ``Nat.mod, ``Nat.modCore, ``Nat.pow, ``Nat.gcd,
    ``Nat.beq, ``Nat.ble, ``Nat.decEq, ``Nat.decLt, ``Nat.decLe, ``Nat.pred, ``Nat.land,
    ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight, ``Nat.log2,
    ``Int.neg, ``Int.add, ``Int.sub, ``Int.mul, ``Int.tdiv, ``Int.tmod, ``Int.ediv, ``Int.emod,
    ``Int.decEq, ``Int.decLt, ``Int.decLe, ``Int.decNonneg, ``Int.natAbs, ``Int.toNat,
    ``mixHash, ``Char.ofNatAux, ``Lean.Name.beq,
    -- Arrays: the operations whose index has a proof, never `!`.
    ``Array.mkEmpty, ``Array.emptyWithCapacity, ``Array.replicate, ``Array.push, ``Array.pop,
    ``Array.size, ``Array.usize, ``Array.getInternal, ``Array.uget, ``Array.set, ``Array.uset,
    ``Array.swap, ``Array.toList,
    ``ByteArray.emptyWithCapacity, ``ByteArray.push, ``ByteArray.size, ``ByteArray.usize,
    ``ByteArray.get, ``ByteArray.uget, ``ByteArray.set, ``ByteArray.uset, ``ByteArray.hash,
    ``ByteArray.beq, ``ByteArray.decEq, ``ByteArray.data,
    ``FloatArray.emptyWithCapacity, ``FloatArray.push, ``FloatArray.size, ``FloatArray.usize,
    ``FloatArray.get, ``FloatArray.uget, ``FloatArray.set, ``FloatArray.uset, ``FloatArray.data,
    -- Strings.
    ``String.push, ``String.append, ``String.length, ``String.utf8ByteSize, ``String.decEq,
    ``String.hash, ``String.data, ``String.toList, ``String.ofList, ``String.toUTF8,
    ``String.Internal.append, ``String.Internal.length]
  for t in ["UInt8", "UInt16", "UInt32", "UInt64", "USize", "Int8", "Int16", "Int32", "Int64",
            "ISize"] do
    for op in fixedWidthOps do s := s.insert (Name.mkStr (Name.mkSimple t) op)
  for t in ["Float", "Float32"] do
    for op in floatOps do s := s.insert (Name.mkStr (Name.mkSimple t) op)
  for t in ["UInt8", "UInt16", "UInt32", "UInt64", "USize", "Int8", "Int16", "Int32", "Int64",
            "ISize"] do
    s := s.insert (Name.mkStr `Bool ("to" ++ t))
  return s

end LeanToReussir
