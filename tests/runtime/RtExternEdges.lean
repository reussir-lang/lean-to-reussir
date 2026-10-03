/-! Runtime test: externs at their edge values, called directly and as
function values in generic code (`table` takes the extern as an argument;
`Ex` packages it in an existential): Int ediv/emod/tdiv/tmod/fdiv/fmod/bmod
over 11 values including ±2^63, ±2^64, 2^70; Nat sub/div/mod/shiftRight/land/
xor including 2^100; UInt8/Int8/UInt64/Int64 div/mod/shl/shr with 0 divisors
and shifts at least the width or negative; Nat.log2/toUSize/toUInt8/toUInt64;
Float to (U)Int8/16/32/64/USize with NaN, ±inf, ±0, 255.9, 1e20,
4294967295.5; Char.ofNat of surrogates and ≥ 0x110000; String.Pos.Raw
get/get?/next/prev/isValid/atEnd/extract/set/modify at every byte of "aé😀b"
and past the end; Substring.Raw with start > stop; Array/ByteArray get!/set!/
extract out of bounds; toUInt64LE! on 3 bytes; USize wrap-around.
From the round-7 review, area L (rv7/lowering), check 16 (LwExtEdge1). -/

-- Extern edge values, called directly and through function values (partial applications of externs)
structure Ex where
  α : Type
  f : α → α → α
  xs : List α
  show' : α → String

@[noinline] def table {α β γ} [ToString γ] (name : String) (f : α → β → γ) (xs : List α) (ys : List β) : IO Unit := do
  let rows := xs.map fun x => ys.map fun y => toString (f x y)
  IO.println s!"{name}: {rows}"

@[noinline] def runEx (e : Ex) : String :=
  toString (e.xs.map fun x => e.xs.map fun y => e.show' (e.f x y))

def ints : List Int := [0, 1, -1, 7, -7, 2^63 - 1, -2^63, 2^64, -(2^64), 2^70 + 3, -(2^70) - 3]
def nats : List Nat := [0, 1, 2, 7, 2^63, 2^64 - 1, 2^64, 2^100 + 1]
def u8s : List UInt8 := [0, 1, 7, 8, 9, 127, 128, 255]
def i8s : List Int8 := [0, 1, -1, 7, -8, 8, 127, -128]
def u64s : List UInt64 := [0, 1, 63, 64, 65, 2^63, 0xFFFFFFFFFFFFFFFF]
def i64s : List Int64 := [0, 1, -1, 63, 64, -64, 9223372036854775807, -9223372036854775808]
def fl : List Float := [0.0, -0.0, 1.5, -1.5, 255.9, 256.0, -255.9, 1e20, -1e20, 0.0/0.0, 1.0/0.0, -1.0/0.0, 4294967295.5, 9.3e18, 1.9e19]

def main : IO Unit := do
  table "Int.div" Int.ediv ints ints
  table "Int.mod" (fun (a b : Int) => a % b) ints ints
  table "Int.ediv" Int.ediv ints ints
  table "Int.emod" Int.emod ints ints
  table "Int.tdiv" Int.tdiv ints ints
  table "Int.tmod" Int.tmod ints ints
  table "Int.fdiv" Int.fdiv ints ints
  table "Int.fmod" Int.fmod ints ints
  table "Int.bmod" Int.bmod ints nats
  table "Nat.sub" Nat.sub nats nats
  table "Nat.div" Nat.div nats nats
  table "Nat.mod" Nat.mod nats nats
  table "Nat.shiftRight" Nat.shiftRight nats [0, 1, 63, 64, 65, 200]
  table "Nat.land" Nat.land nats nats
  table "Nat.xor" Nat.xor nats nats
  table "U8.div" UInt8.div u8s u8s
  table "U8.mod" UInt8.mod u8s u8s
  table "U8.shl" UInt8.shiftLeft u8s u8s
  table "U8.shr" UInt8.shiftRight u8s u8s
  table "I8.div" Int8.div i8s i8s
  table "I8.mod" Int8.mod i8s i8s
  table "I8.shl" Int8.shiftLeft i8s i8s
  table "I8.shr" Int8.shiftRight i8s i8s
  table "U64.div" UInt64.div u64s u64s
  table "U64.shl" UInt64.shiftLeft u64s u64s
  table "U64.shr" UInt64.shiftRight u64s u64s
  table "I64.div" Int64.div i64s i64s
  table "I64.mod" Int64.mod i64s i64s
  table "I64.shr" Int64.shiftRight i64s i64s
  IO.println s!"log2 {nats.map Nat.log2} {(nats.map Nat.toUSize)} {nats.map Nat.toUInt8} {nats.map Nat.toUInt64}"
  IO.println s!"f2u8 {fl.map Float.toUInt8} f2u64 {fl.map Float.toUInt64} f2i8 {fl.map Float.toInt8} f2i64 {fl.map Float.toInt64} f2usize {fl.map Float.toUSize}"
  IO.println s!"f2i32 {fl.map Float.toInt32} f2u32 {fl.map Float.toUInt32} f32 {fl.map (fun f => f.toFloat32.toUInt16)}"
  let cps : List Nat := [0, 0x41, 0xD7FF, 0xD800, 0xDFFF, 0xE000, 0x10FFFF, 0x110000, 2^32 + 65, 2^64 + 66]
  IO.println s!"chars {cps.map (fun n => (Char.ofNat n).toNat)} {cps.map (fun n => (Char.ofNat n))}"
  let s := "aé😀b"
  let poss : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 100]
  IO.println s!"get {poss.map (fun p => String.Pos.Raw.get s ⟨p⟩)} next {poss.map (fun p => (String.Pos.Raw.next s ⟨p⟩).byteIdx)} prev {poss.map (fun p => (String.Pos.Raw.prev s ⟨p⟩).byteIdx)}"
  IO.println s!"get? {poss.map (fun p => String.Pos.Raw.get? s ⟨p⟩)} valid {poss.map (fun p => String.Pos.Raw.isValid s ⟨p⟩)} atEnd {poss.map (fun p => String.Pos.Raw.atEnd s ⟨p⟩)}"
  IO.println s!"extract {poss.map (fun p => String.Pos.Raw.extract s ⟨p⟩ ⟨p + 3⟩)} {poss.map (fun p => String.Pos.Raw.extract s ⟨p + 3⟩ ⟨p⟩)}"
  IO.println s!"set {poss.map (fun p => String.Pos.Raw.set s ⟨p⟩ 'Z')} modify {poss.map (fun p => String.Pos.Raw.modify s ⟨p⟩ Char.toUpper)}"
  let subs : List (Nat × Nat) := [(0, 2), (1, 3), (2, 1), (3, 100), (100, 200), (6, 6)]
  IO.println s!"substr {subs.map (fun (a, b) => (Substring.Raw.mk s ⟨a⟩ ⟨b⟩).toString)} {subs.map (fun (a, b) => (Substring.Raw.mk s ⟨a⟩ ⟨b⟩).bsize)} {subs.map (fun (a, b) => (Substring.Raw.mk s ⟨a⟩ ⟨b⟩).front)}"
  let arr := #[10, 20, 30]
  IO.println s!"arr {[0, 2, 3, 2^64].map (fun i => arr[i]!)} {[0, 3].map (fun i => (arr.set! i 99))} {arr.swapIfInBounds 0 7} {arr.extract 2 1} {arr.extract 1 100}"
  let bs : ByteArray := ⟨#[1, 2, 3]⟩
  IO.println s!"bytes {[0, 3].map (fun i => bs[i]!)} {[0, 5].map (fun i => bs.set! i 9)} {bs.extract 2 1} {bs.toUInt64LE!}"
  IO.println s!"usize {USize.size} {(0 : USize) - 1} {USize.ofNat (2^64 + 5)} {(2^64 - 1 : Nat).toUSize.toNat}"
  -- through uniform code
  let exs : List Ex := [⟨Int, Int.tdiv, [7, -7, 0, -2^63], toString⟩, ⟨UInt8, UInt8.shiftLeft, [1, 8, 9, 255], toString⟩,
    ⟨Nat, Nat.sub, [0, 5, 2^64], toString⟩, ⟨Int8, Int8.div, [-128, -1, 0, 3], toString⟩,
    ⟨Float, Float.div, [0, -0.0, 1, 0/0], toString⟩, ⟨String, String.append, ["", "é"], id⟩]
  for e in exs do IO.println (runEx e)
  table "fdivmix" (fun (a : Int) (b : Int) => (a.fdiv b, a.fmod b, a.tdiv b, a.tmod b)) [-7, 7, -2^63] [2, -2, 0, -1]

