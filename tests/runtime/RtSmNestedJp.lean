/-! Runtime test: a DEFLATE-style decoder loop with the shape of lean-zip's
inflate loop (`InflateBuf.goTreeFreeU`): a refill branch, a fast literal
path, and a slow path that is a join point outlined into the loop's state
machine (J4). The slow path has join points of its own: the `||` condition
of the inlined table lookup (`decodeSym`, `subLookup`), the `Except` results
of the inlined `takeBits` and `decodeSym`, and `let`s whose values come
from an `if`. Every path of such an inner join point's scope jumps to it,
so it is a structured `let` (J2) inside the outlined body that declares it,
not a variant of the state machine: the state machine has 5 variants, not
10, and LLVM's DFAJumpThreading threads its loop (it threads a loop of at
most 7 states). The default size is small (20000).
tests/runtime/sm-slots-check.sh checks the `.rr` and the LLVM IR of this
program. -/

@[inline] def unpackLen (e : UInt32) : UInt8 := e.toUInt8
@[inline] def unpackSym (e : UInt32) : UInt16 := (e >>> 8).toUInt16

@[inline] def takeBits (bitBuf : UInt64) (cnt n : Nat) : Except String (Nat × UInt64 × Nat) :=
  if n > cnt then .error "takeBits: out of bits"
  else .ok ((bitBuf &&& ((1 <<< n.toUInt64) - 1)).toNat, bitBuf >>> n.toUInt64, cnt - n)

/-- A long code: the root entry holds a sub-table offset (plus one). -/
@[inline] def subLookup (subs : Array UInt32) (table : Array UInt32) (bitBuf : UInt64) (cnt : Nat) :
    Except String (UInt16 × UInt64 × Nat) :=
  let rootE := table[(bitBuf &&& 0x7FF).toNat]!
  if unpackLen rootE ≠ 0 then .error "invalid code"
  else
    let off1 := (unpackSym rootE).toNat
    if off1 == 0 then .error "invalid code"
    else
      let e := subs[off1 - 1 + ((bitBuf >>> 11) &&& 0xF).toNat]!
      let len := (unpackLen e).toNat
      if len == 0 then .error "invalid code"
      else if len > cnt then .error "out of bits"
      else .ok (unpackSym e, bitBuf >>> len.toUInt64, cnt - len)

@[inline] def decodeSym (subs table : Array UInt32) (bitBuf : UInt64) (cnt : Nat) :
    Except String (UInt16 × UInt64 × Nat) :=
  let e := table[(bitBuf &&& 0x7FF).toNat]!
  let len := (unpackLen e).toNat
  if len == 0 || len > cnt then subLookup subs table bitBuf cnt
  else .ok (unpackSym e, bitBuf >>> len.toUInt64, cnt - len)

def lengthBase : Array UInt16 := #[3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31,
  35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258]
def lengthExtra : Array UInt8 := #[0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2,
  3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0]

@[noinline] def copyBack (out : ByteArray) (dist len : Nat) : ByteArray := Id.run do
  let mut o := out
  let start := out.size - dist
  for k in [0:len] do
    o := o.push o[start + k % dist]!
  return o

partial def decode (lit dist litSubs distSubs : Array UInt32) (data : ByteArray) (maxOut : Nat)
    (pos : USize) (bitBuf : UInt64) (cnt : USize) (out : ByteArray) :
    Except String (ByteArray × USize × UInt64 × USize) :=
  if cnt ≤ 56 ∧ pos < data.size.toUSize then
    decode lit dist litSubs distSubs data maxOut (pos + 1)
      (bitBuf ||| ((data[pos.toNat]!).toUInt64 <<< cnt.toUInt64)) (cnt + 8) out
  else
  let e := lit[(bitBuf &&& 0x7FF).toNat]!
  if unpackLen e ≠ 0 ∧ (unpackLen e).toUSize ≤ cnt ∧ unpackSym e < 256 then
    if out.size ≥ maxOut then .ok (out, pos, bitBuf, cnt)
    else
      decode lit dist litSubs distSubs data maxOut pos (bitBuf >>> (unpackLen e).toUInt64)
        (cnt - (unpackLen e).toUSize) (out.push (unpackSym e).toUInt8)
  else
  let cnt0 := cnt.toNat
  match decodeSym litSubs lit bitBuf cnt0 with
  | .error err => if pos.toNat ≥ data.size then .ok (out, pos, bitBuf, cnt) else .error err
  | .ok (sym, bitBuf, cnt') =>
    if sym < 256 then
      if out.size ≥ maxOut then .ok (out, pos, bitBuf, cnt'.toUSize)
      else if cnt0 ≤ cnt' then .error "no progress"
      else decode lit dist litSubs distSubs data maxOut pos bitBuf cnt'.toUSize (out.push sym.toUInt8)
    else if sym == 256 then .ok (out, pos, bitBuf, cnt'.toUSize)
    else
      let idx := sym.toNat - 257
      if idx ≥ lengthBase.size then .error s!"invalid length code {sym}"
      else
        match takeBits bitBuf cnt' lengthExtra[idx]!.toNat with
        | .error err => .error err
        | .ok (extraBits, bitBuf, cnt'') =>
        let length := if idx < 28 then lengthBase[idx]!.toNat + extraBits else 258
        match decodeSym distSubs dist bitBuf cnt'' with
        | .error err => if pos.toNat ≥ data.size then .ok (out, pos, bitBuf, cnt''.toUSize) else .error err
        | .ok (dSym, bitBuf, cnt3) =>
          match takeBits bitBuf cnt3 (dSym % 8).toNat with
          | .error err => .error err
          | .ok (dExtraBits, bitBuf, cnt4) =>
            let base := if dSym < 4 then dSym.toNat else dSym.toNat * 8
            let distance := if dSym < 4 then base + 1 else base + dExtraBits + 1
            if distance > out.size then
              if out.size == 0 then .error "zero-size back-reference"
              else
                decode lit dist litSubs distSubs data maxOut pos bitBuf cnt4.toUSize
                  (copyBack out out.size length)
            else if out.size + length > maxOut then .ok (out, pos, bitBuf, cnt4.toUSize)
            else if cnt0 ≤ cnt4 then .error "no progress"
            else decode lit dist litSubs distSubs data maxOut pos bitBuf cnt4.toUSize
              (copyBack out distance length)

/-- An LCG for the input bytes and the tables. -/
def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- A root table: most slots are codes of `lo`..`lo+5` bits, every 128th a
long code (length 0, a sub-table offset), every 64th (literal table only) a
length code. -/
def mkTable (seed : UInt64) (lo : UInt64) (lens : Bool) : Array UInt32 := Id.run do
  let mut t := Array.emptyWithCapacity 2048
  let mut s : UInt64 := seed
  for i in [0:2048] do
    s := lcg s
    let len : UInt32 := (lo + (s >>> 33) % 6).toUInt32
    let e : UInt32 :=
      if i % 128 == 127 then ((((i / 128) * 16 + 1 : Nat).toUInt32) <<< 8)
      else if lens && i % 64 == 5 then ((((257 : UInt64) + (s >>> 40) % 28).toUInt32) <<< 8) ||| len
      else ((((s >>> 45) % (if lens then 256 else 128)).toUInt32) <<< 8) ||| len
    t := t.push e
  return t

/-- The sub-tables: 16 blocks of 16 entries, codes of 12..15 bits; slot 0 of
every 4th block is a hole (an invalid code). -/
def mkSubs (seed : UInt64) (lens : Bool) : Array UInt32 := Id.run do
  let mut t := Array.emptyWithCapacity 256
  let mut s : UInt64 := seed
  for i in [0:256] do
    s := lcg s
    let len : UInt32 := ((12 : UInt64) + (s >>> 33) % 4).toUInt32
    let sym : UInt32 := ((s >>> 45) % (if lens then 285 else 128)).toUInt32
    t := t.push (if i % 64 == 0 then (0 : UInt32) else (sym <<< 8) ||| len)
  return t

def mkData (n : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity n
  let mut s : UInt64 := 3
  for _ in [0:n] do
    s := lcg s
    b := b.push (s >>> 56).toUInt8
  return b

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 20000
  let data := mkData n
  let lit := mkTable 7 6 true
  let dist := mkTable 11 5 false
  let litSubs := mkSubs 13 true
  let distSubs := mkSubs 17 false
  let mut total := 0
  let mut h : UInt64 := 0
  -- Rounds 4 and 5 stop at the output limit; round 6 decodes a truncated
  -- input (an error exit in the middle of a symbol or not).
  for round in [0:7] do
    let maxOut := if round == 4 then 1000 else if round == 5 then n else n * 4
    let input := if round == 6 then data.extract 0 (n / 3) else data
    match decode lit dist litSubs distSubs input maxOut 0 (round.toUInt64 * 3) round.toUSize ByteArray.empty with
    | .error e => IO.println s!"round {round}: error {e}"
    | .ok (out, pos, bb, cnt) =>
      total := total + out.size
      for i in [0:out.size:97] do
        h := h * 31 + out[i]!.toUInt64
      IO.println s!"round {round}: out {out.size} pos {pos} bitBuf {bb % 1000} cnt {cnt}"
  IO.println s!"total {total} hash {h}"
