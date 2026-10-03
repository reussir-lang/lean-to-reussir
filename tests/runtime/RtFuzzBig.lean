/-! Runtime test: big numbers. DBig: 600 random many-limb `Nat`/`Int` values
(0..22 limbs, zero and all-ones limbs; fixed LCG seed) checked against
identities (divmod, truncating sub, distributivity, xor/and/or, shifts,
gcd/lcm, log2, sqrt, pow, ediv/emod/tdiv/fdiv/bmod, neg, toNat, complement,
`>>>`) and printed (conversions, toFloat, hex, testBit, hashes); in-place loops
on unique big values. DAlias: `x+x`, `x-x`, `x*x`, `x/x`, `x%x`, bitwise ops,
gcd/lcm, `^2` with both operands the same unique big value; `s ++ s`,
`a ++ a`, `a.push a.size`, `b ++ b`, `copySlice` with src = dest.
From the round-7 review, area D (rv7/rtdata), checks DBig and DAlias. -/

namespace DBig
-- from rv7/rtdata/DBig.lean
-- Random many-limb Nat/Int arithmetic identities and printouts.
def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

-- A random Nat of `limbs` 64-bit limbs with some all-ones / zero limbs.
def mkNat (seed : UInt64) (limbs : Nat) : Nat := Id.run do
  let mut s := seed
  let mut r : Nat := 0
  for _ in [0:limbs] do
    s := lcg s
    let kind := (s >>> 60).toNat
    let limb : Nat := if kind == 0 then 0 else if kind == 1 then 2^64 - 1 else if kind == 2 then 1 else ((lcg s) ^^^ (s >>> 17)).toNat
    r := r * 2^64 + limb
  return r

def check (lbl : String) (b : Bool) : IO Unit :=
  unless b do IO.println s!"FAIL {lbl}"

def main : IO Unit := do
  let mut acc : UInt64 := 0
  for k in [0:600] do
    let la := k % 23
    let lb := (k * 7 + 3) % 17
    let a := mkNat (k.toUInt64 * 31 + 5) la
    let b := mkNat (k.toUInt64 * 131 + 11) lb
    let c := mkNat (k.toUInt64 * 1031 + 17) (k % 5)
    -- identities
    check s!"{k} divmod" (b == 0 || (a / b) * b + a % b == a)
    check s!"{k} mod<" (b == 0 || a % b < b)
    check s!"{k} sub" ((a + b) - b == a)
    check s!"{k} trunc" (a - (a + b + 1) == 0)
    check s!"{k} distr" (a * (b + c) == a * b + a * c)
    check s!"{k} xor" ((a ^^^ b) ^^^ b == a)
    check s!"{k} andor" ((a &&& b) + (a ||| b) == a + b)
    check s!"{k} shl" ((a <<< (k % 200)) >>> (k % 200) == a)
    check s!"{k} shl2" (a <<< (k % 130) == a * 2 ^ (k % 130))
    check s!"{k} shr" (a >>> (k % 150) == a / 2 ^ (k % 150))
    check s!"{k} gcd" (Nat.gcd a b == Nat.gcd b (a % (if b == 0 then 1 else b)) || b == 0)
    check s!"{k} lcm" (a == 0 || b == 0 || Nat.lcm a b * Nat.gcd a b == a * b)
    check s!"{k} log2" (a == 0 || (2 ^ Nat.log2 a ≤ a && a < 2 ^ (Nat.log2 a + 1)))
    check s!"{k} sqrt" (let r := Nat.sqrt a; r * r ≤ a && a < (r + 1) * (r + 1))
    check s!"{k} pow" (b ^ 3 == b * b * b)
    -- signed
    let ia : Int := if k % 2 == 0 then a else -(a : Int)
    let ib : Int := if k % 3 == 0 then b else -(b : Int)
    check s!"{k} ediv" (ib == 0 || ia / ib * ib + ia % ib == ia)
    check s!"{k} emod" (ib == 0 || (0 ≤ ia % ib && ia % ib < ib.natAbs))
    check s!"{k} tdiv" (ib == 0 || ia.tdiv ib * ib + ia.tmod ib == ia)
    check s!"{k} fdiv" (ib == 0 || ia.fdiv ib * ib + ia.fmod ib == ia)
    check s!"{k} bmod" (ib == 0 || (ia.bmod b.succ - ia) % (b.succ : Int) == 0)
    check s!"{k} neg" (-(-ia) == ia && ia + (-ia) == 0)
    check s!"{k} toNat" (ia.toNat == (if ia < 0 then 0 else a))
    check s!"{k} lnot" (~~~(~~~ia) == ia && ~~~ia == -ia - 1)
    check s!"{k} shiftR" (ia >>> (k % 100) == ia / (2 ^ (k % 100) : Nat))
    acc := mixHash acc (hash a) |> mixHash (hash ia) |> mixHash (hash (a / (b + 1)))
    if k % 25 == 0 then
      IO.println s!"{k}: a={a} b={b}"
      IO.println s!"  q={a / (b+1)} r={a % (b+1)} p={a * b} x={a ^^^ b} o={a ||| b} n={a &&& b}"
      IO.println s!"  iq={ia / ib} ir={ia % ib} tq={ia.tdiv ib} tr={ia.tmod ib} fq={ia.fdiv ib} fr={ia.fmod ib}"
      IO.println s!"  u64={a.toUInt64} i64={ia.toInt64} u8={a.toUInt8} i8={ia.toInt8} f={a.toFloat} if={Float.ofInt ia} hex={String.ofList (Nat.toDigits 16 a)}"
      IO.println s!"  g={Nat.gcd a b} l2={Nat.log2 a} sq={Nat.sqrt a} tb={a.testBit 64} {a.testBit 127} hash={hash a} ihash={hash ia}"
  IO.println s!"acc {acc}"
  -- in-place loops on unique big values
  let mut f : Nat := 1
  for i in [1:400] do
    f := f * i + (i % 7)
  let mut g := f
  for i in [1:300] do
    g := g / (i + 1) + i
  let mut h := f
  for i in [0:200] do
    h := h - (i * 1000003)
  let mut sh := f
  for i in [0:100] do
    sh := (sh <<< (i % 70)) >>> (i % 65)
  IO.println s!"f={f % (2^64)} g={g} h={h % 1000000007} sh={sh % 1000000007} {f.log2} {sh.log2}"
  let mut z : Int := -(f : Int)
  for i in [1:300] do
    z := z / (i : Int) - (i : Int) * 3
  IO.println s!"z={z}"
end DBig

namespace DAlias
-- from rv7/rtdata/DAlias.lean
-- Operations whose two operands are the same (unique) value.
@[noinline] def mkBig (k : Nat) : Nat := 2^130 + 2^64 * k + 12345 + k
@[noinline] def mkStr (k : Nat) : String := "ab€" ++ toString k
@[noinline] def mkArr (k : Nat) : Array Nat := #[k, 2^70 + k, 3]
@[noinline] def mkBytes (k : Nat) : ByteArray := ByteArray.mk #[1, 2, k.toUInt8]

@[noinline] def selfAdd (x : Nat) : Nat := x + x
@[noinline] def selfSub (x : Nat) : Nat := x - x
@[noinline] def selfMul (x : Nat) : Nat := x * x
@[noinline] def selfDiv (x : Nat) : Nat := x / x
@[noinline] def selfMod (x : Nat) : Nat := x % x
@[noinline] def selfOps (x : Nat) : List Nat := [x &&& x, x ||| x, x ^^^ x, Nat.gcd x x, Nat.lcm x x, x ^ 2]
@[noinline] def iself (x : Int) : List Int := [x + x, x - x, x * x, x / x, x % x, x.tdiv x, x.fmod x, -x + x]

def main : IO Unit := do
  for k in [0:5] do
    let x := mkBig k
    IO.println s!"{selfAdd x} {selfSub x} {selfMul x} {selfDiv x} {selfMod x} {selfOps x}"
    IO.println s!"{iself (-(x : Int))} {iself (x : Int)}"
    let y := mkBig (k + 10)
    let z := y + y + y
    IO.println s!"{z} {z * z - z} {(z - y) / y}"
    let s := mkStr k
    let t := s ++ s
    IO.println s!"{t} {t.length} {(s ++ s ++ s).length}"
    let s2 := mkStr k
    let u := s2.append s2
    IO.println s!"{u} {u.length}"
    let a := mkArr k
    let b := a ++ a
    IO.println s!"{b} {b.size}"
    let a2 := mkArr k
    IO.println s!"{a2.push a2.size} {(a2.append a2).size}"
    let bs := mkBytes k
    IO.println s!"{(bs ++ bs).toList} {(bs.copySlice 0 bs 2 3).toList} {(bs.copySlice 1 bs 0 5 false).toList}"
    let f : FloatArray := ⟨#[1.5, 2.5, k.toFloat]⟩
    IO.println s!"{(f.push f.size.toFloat).toList}"
end DAlias

def main : IO Unit := do
  IO.println "=== DBig"
  DBig.main
  IO.println "=== DAlias"
  DAlias.main
