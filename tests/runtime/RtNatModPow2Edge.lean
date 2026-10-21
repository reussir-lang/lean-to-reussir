/-! Runtime test: shapes of `x % 2^w` beside RtNatModPow2's (the
optimization `mod-pow2` computes it as the low `w` bits of `x`; runtime bug
hunt, 2026-10-21): a power kept because it has another use, `p % p` and
`w % 2^w`, constants that are literal powers (`2^100`, `2^63`,
`UInt64.size`, `USize.size`), a shared literal 1 or 2, `% 2^w` inside a
closure, the Int divisions by `2^w` (never rewritten), `BitVec.ofInt` and
`toInt`, BitVec operations at widths 0, 1, 5, 64, 65 and 129, and big
numbers around the big-number paths that the same branch changed (a
division whose dividend is smaller than its divisor, with both signs;
bitwise results whose top limbs are zero). -/

def M100 : Nat := 2 ^ 100
def M63 : Nat := 2 ^ 63

-- 2^w kept: also used as a value.
@[noinline] def keepPow (x w : Nat) : Nat × Nat := let p := 2 ^ w; (x % p, p - 1)
-- the power modulo itself, and w modulo 2^w
@[noinline] def selfMod (w : Nat) : Nat × Nat := let p := 2 ^ w; (p % p, w % p)
-- user constants that are literal powers, UInt64.size, USize.size
@[noinline] def constMods (x : Nat) : List Nat := [x % M100, x % M63, x % UInt64.size, x % USize.size, x % (2 ^ 64 + 0)]
-- shared literal 1 and 2
@[noinline] def sharedOne (x w : Nat) : Nat × Nat := let one := 1; (x % (one <<< w), x + one)
@[noinline] def sharedTwo (x w : Nat) : Nat × Nat := let two := 2; (x % (two ^ w), two ^ (w + 1))
-- inside a closure
@[noinline] def mapMod (xs : List Nat) (w : Nat) : List Nat := xs.map (· % 2 ^ w)
-- Int: never rewritten
@[noinline] def intMods (x : Int) (w : Nat) : List Int :=
  [x % (2 ^ w : Nat), x % (2 ^ w : Int), Int.emod x (2 ^ w), Int.tmod x (2 ^ w), Int.fmod x (2 ^ w),
   x / (2 ^ w : Int), Int.tdiv x (2 ^ w), Int.fdiv x (2 ^ w), (BitVec.ofInt w x).toInt, ((BitVec.ofInt w x).toNat : Int)]
-- BitVec at width 0 and from args
@[noinline] def bvOps (w x y : Nat) : List Nat :=
  let a := BitVec.ofNat w x
  let b := BitVec.ofNat w y
  [(a + b).toNat, (a * b).toNat, (a - b).toNat, (a <<< (w / 2)).toNat, (a >>> 3).toNat, (-a).toNat,
   (a ^^^ b).toNat, (a &&& b).toNat, (a ||| b).toNat, (BitVec.allOnes w).toNat, (a / b).toNat, (a % b).toNat,
   (a.signExtend (w + 70)).toNat, (a.zeroExtend (w + 70)).toNat, (a ++ b).toNat, (a.rotateLeft 5).toNat]

/-- A big number made here (unique when used). -/
@[noinline] def fresh (k : Nat) : Nat := 3 ^ (k + 200) + k

def main (args : List String) : IO Unit := do
  let base := (args.head? >>= String.toNat?).getD 0
  let ws := [0, 1, 63, 64, 65, 128, 129, 300].map (· + base)
  let xs := [0, 1, 2 ^ 63 - 1, 2 ^ 63, 2 ^ 64 - 1, 2 ^ 64 + 3, 2 ^ 128 + 2 ^ 64, 3 ^ 300].map (· + base)
  for w in ws do
    IO.println s!"w={w} {selfMod w} {mapMod xs w}"
    for x in xs do
      IO.println s!"  {keepPow x w} {sharedOne x w} {sharedTwo x w}"
  for x in xs do
    IO.println s!"c {constMods x}"
  for w in [0, 1, 31, 32, 63, 64, 65, 130].map (· + base) do
    for x in [(0 : Int), 1, -1, -5, 2 ^ 31, -2 ^ 31, -2 ^ 63, -(2 ^ 64) - 3, 2 ^ 130 + 7, -(3 ^ 100)] do
      IO.println s!"i {w} {x}: {intMods (x + base) w}"
  for w in [0, 1, 5, 64, 65, 129].map (· + base) do
    IO.println s!"bv {w}: {bvOps w (fresh w) (2 ^ (w + 1) + 7)} {bvOps w 3 0}"
  -- big divisions with |a| < |b|, negative dividends, unique and shared
  let b := fresh 50
  for a in [fresh 1, fresh 2, b, b - 1, b + 1] do
    let na : Int := -(a : Int)
    let bi : Int := b
    IO.println s!"d {a % b} {a / b} {na / bi} {na % bi} {na / (-bi)} {na % (-bi)} {Int.tdiv na bi} {Int.tmod na bi} {Int.fdiv na bi} {Int.fmod na (-bi)} {a}"
  -- bitwise on big numbers: shared and unique, results with zero top limbs
  let s := fresh 10
  for k in [0, 1, 2, 3] do
    let u := fresh (10 + k)
    IO.println s!"b {u ^^^ s} {s &&& u} {fresh (10 + k) ||| s} {(fresh 10) ^^^ s} {s >>> (64 * k + 1)} {(s <<< (64 * k + 3)) >>> (64 * k + 3) == s} {s}"
