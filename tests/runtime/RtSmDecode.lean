/-! Runtime test: a table-driven bit decoder with the shape of a DEFLATE
inner loop (a refill branch, a fast literal path through an 11-bit table, a
slow path returning `Except`, back-references with extra bits and a copy).
Its compound conditions make join points with two or three jumps, so the
loop is a state machine (J4). With the optional pass `state-machines`, every
variant of its entry enum is nullary, so the enum is a `[value]` enum (a
scalar tag, no pointer to a static cell whose count is tested at every
entry), and a jump passes the slots that its arm does not bind on
unchanged. The output buffer, pushed at every step, stays unshared across
the jumps: `dbgTraceIfShared` prints `shared RC out shared (literal)` once
per round, for the first push to the initial `ByteArray.empty` (a shared
constant), as natively, and never for a buffer the loop has built. The
default size is small (20000).
tests/runtime/sm-slots-check.sh checks the `.rr` and the LLVM IR of this
program. -/

@[inline] def unpackLen (e : UInt32) : UInt8 := e.toUInt8
@[inline] def unpackSym (e : UInt32) : UInt16 := (e >>> 8).toUInt16

@[inline] def takeBits (bitBuf : UInt64) (cnt n : Nat) : Except String (Nat × UInt64 × Nat) :=
  if n > cnt then .error "takeBits: out of bits"
  else .ok ((bitBuf &&& ((1 <<< n.toUInt64) - 1)).toNat, bitBuf >>> n.toUInt64, cnt - n)

/-- The slow path: a 12-bit code giving a length code 257..284. -/
@[noinline] def slowSym (bitBuf : UInt64) (cnt : Nat) : Except String (UInt16 × UInt64 × Nat) :=
  if cnt < 12 then .error "slowSym: out of bits"
  else .ok ((bitBuf &&& 0xFFF).toUInt16 % 28 + 257, bitBuf >>> 12, cnt - 12)

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

partial def decode (lit dist : Array UInt32) (data : ByteArray) (maxOut : Nat)
    (pos : USize) (bitBuf : UInt64) (cnt : USize) (out : ByteArray) :
    Except String (ByteArray × USize × UInt64 × USize) := do
  if cnt ≤ 56 ∧ pos < data.size.toUSize then
    decode lit dist data maxOut (pos + 1)
      (bitBuf ||| ((data[pos.toNat]!).toUInt64 <<< cnt.toUInt64)) (cnt + 8) out
  else
  let e := lit[(bitBuf &&& 0x7FF).toNat]!
  if unpackLen e ≠ 0 ∧ (unpackLen e).toUSize ≤ cnt ∧ unpackSym e < 256 then
    if out.size ≥ maxOut then .ok (out, pos, bitBuf, cnt)
    else
      let out := dbgTraceIfShared "out shared (literal)" out
      decode lit dist data maxOut pos (bitBuf >>> (unpackLen e).toUInt64)
        (cnt - (unpackLen e).toUSize) (out.push (unpackSym e).toUInt8)
  else
  let cnt0 := cnt.toNat
  let r : Except String (UInt16 × UInt64 × Nat) :=
    if unpackLen e ≠ 0 ∧ (unpackLen e).toNat ≤ cnt0 then
      .ok (unpackSym e, bitBuf >>> (unpackLen e).toUInt64, cnt0 - (unpackLen e).toNat)
    else slowSym bitBuf cnt0
  match r with
  | .error err => if pos.toNat ≥ data.size then .ok (out, pos, bitBuf, cnt) else .error err
  | .ok (sym, bitBuf, cnt') =>
    if sym < 256 then
      if out.size ≥ maxOut then .ok (out, pos, bitBuf, cnt'.toUSize)
      else decode lit dist data maxOut pos bitBuf cnt'.toUSize (out.push sym.toUInt8)
    else if sym == 256 then .ok (out, pos, bitBuf, cnt'.toUSize)
    else
      let idx := sym.toNat - 257
      if idx ≥ lengthBase.size then throw s!"invalid length code {sym}"
      else
        let (extraBits, bitBuf, cnt'') ← takeBits bitBuf cnt' lengthExtra[idx]!.toNat
        let length := lengthBase[idx]!.toNat + extraBits
        let d := dist[(bitBuf &&& 0x7FF).toNat]!
        if unpackLen d == 0 || (unpackLen d).toNat > cnt'' then
          if pos.toNat ≥ data.size then .ok (out, pos, bitBuf, cnt''.toUSize)
          else throw s!"invalid distance code at {pos}"
        else
          let bitBuf := bitBuf >>> (unpackLen d).toUInt64
          let cnt3 := cnt'' - (unpackLen d).toNat
          let (dExtraBits, bitBuf, cnt4) ← takeBits bitBuf cnt3 ((unpackSym d) % 8).toNat
          let distance := (unpackSym d).toNat * 8 + dExtraBits + 1
          let out := dbgTraceIfShared "out shared (copy)" out
          if distance > out.size then
            if out.size == 0 then throw "zero-size back-reference"
            else
              decode lit dist data maxOut pos bitBuf cnt4.toUSize
                (copyBack out out.size length)
          else if out.size + length > maxOut then .ok (out, pos, bitBuf, cnt4.toUSize)
          else if cnt0 ≤ cnt4 then throw "no progress"
          else decode lit dist data maxOut pos bitBuf cnt4.toUSize (copyBack out distance length)

/-- An LCG for the input bytes and the tables. -/
def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- The literal table: most slots are literals of 6..11 bits, a few a
length code (every 64th) or a miss (every 128th, the slow path). -/
def mkLit : Array UInt32 := Id.run do
  let mut t := Array.emptyWithCapacity 2048
  let mut s : UInt64 := 7
  for i in [0:2048] do
    s := lcg s
    let len : UInt32 := ((6 : UInt64) + (s >>> 33) % 6).toUInt32
    let e : UInt32 :=
      if i % 128 == 127 then 0
      else if i % 64 == 5 then ((((257 : UInt64) + (s >>> 40) % 28).toUInt32) <<< 8) ||| len
      else ((((s >>> 45) % 256).toUInt32) <<< 8) ||| len
    t := t.push e
  return t

/-- The distance table: codes of 5..11 bits, symbols 0..127. -/
def mkDist : Array UInt32 := Id.run do
  let mut t := Array.emptyWithCapacity 2048
  let mut s : UInt64 := 11
  for _ in [0:2048] do
    s := lcg s
    let len : UInt32 := ((5 : UInt64) + (s >>> 33) % 7).toUInt32
    t := t.push (((((s >>> 41) % 128).toUInt32) <<< 8) ||| len)
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
  let lit := mkLit
  let dist := mkDist
  let mut total := 0
  let mut h : UInt64 := 0
  -- Rounds 4 and 5 stop at the output limit; round 6 decodes a truncated
  -- input (an error exit in the middle of a back-reference or not).
  for round in [0:7] do
    let maxOut := if round == 4 then 1000 else if round == 5 then n else n * 4
    let input := if round == 6 then data.extract 0 (n / 3) else data
    match decode lit dist input maxOut 0 (round.toUInt64 * 3) round.toUSize ByteArray.empty with
    | .error e => IO.println s!"round {round}: error {e}"
    | .ok (out, pos, bb, cnt) =>
      total := total + out.size
      for i in [0:out.size:97] do
        h := h * 31 + out[i]!.toUInt64
      IO.println s!"round {round}: out {out.size} pos {pos} bitBuf {bb % 1000} cnt {cnt}"
  IO.println s!"total {total} hash {h}"
