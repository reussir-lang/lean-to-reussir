/-! Runtime test: `x % 2^w` computed as the low `w` bits of `x`
(optimization `mod-pow2`, `l2r_nat_truncate_bits`), without making `2^w`.
The outputs must equal native's for:
- the three forms the rule takes: `x % 2 ^ w`, `x % (1 <<< w)` and a
  literal `2^k` with `k ≥ 63` (`x % 2 ^ 64`, `x % 2 ^ 128`, `x % 2 ^ 63`;
  `x % 2 ^ 62` is a small divisor the rule leaves alone);
- `BitVec.ofNat w x` and the `BitVec` operations that end with it (`+`,
  `*`, `<<<`, `1#w`, lean-regex's `b ||| (1#w <<< i)`), at widths from the
  command line (not folded) and at literal widths 64 and 128;
- `w` = 0, 1, 62, 63, 64, 65, 127, 128, 129, 200, 1000 and 2^20 (a power
  of 128 KB natively), `x` small and big (2^63, 2^64 - 1, 2^64 + 5,
  2^128 - 1, 3^500, ...), below and above `2^w`;
- a big `x` used again after the truncation (shared: copied, never written
  in place) and one made just before (unique: truncated in its block).
A width of 2^32 or more ends the native program (`Nat.pow exponent is too
big`); the unit test `nat::tests::truncate_bits` checks those.
`RtNatModPow2.l2r-debug`: the rule rewrites calls here, and the extern it
adds does not make the program one that casts (an axiom did). -/

@[noinline] def modPow (x w : Nat) : Nat := x % 2 ^ w
@[noinline] def modShl (x w : Nat) : Nat := x % (1 <<< w)
@[noinline] def mod64 (x : Nat) : Nat := x % 2 ^ 64
@[noinline] def mod128 (x : Nat) : Nat := x % 2 ^ 128
@[noinline] def mod63 (x : Nat) : Nat := x % 2 ^ 63
@[noinline] def mod62 (x : Nat) : Nat := x % 2 ^ 62
@[noinline] def ofNatW (w x : Nat) : Nat := (BitVec.ofNat w x).toNat
@[noinline] def addW (w x y : Nat) : Nat := (BitVec.ofNat w x + BitVec.ofNat w y).toNat
@[noinline] def mulW (w x y : Nat) : Nat := (BitVec.ofNat w x * BitVec.ofNat w y).toNat
@[noinline] def shlW (w x i : Nat) : Nat := (BitVec.ofNat w x <<< i).toNat
@[noinline] def setBit {w : Nat} (b : BitVec w) (i : Nat) : BitVec w := b ||| (1#w <<< i)
@[noinline] def add64 (x y : BitVec 64) : BitVec 64 := x + y
@[noinline] def mul128 (x y : BitVec 128) : BitVec 128 := x * y

/-- A big number made here (unique when truncated). -/
@[noinline] def fresh (k : Nat) : Nat := 3 ^ (k + 300) + k

def main (args : List String) : IO Unit := do
  let base := (args.head? >>= String.toNat?).getD 0
  let ws := [0, 1, 62, 63, 64, 65, 127, 128, 129, 200, 1000, 2 ^ 20].map (· + base)
  let xs := [0, 1, 5, 2 ^ 62 - 1, 2 ^ 63 - 1, 2 ^ 63, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 64 + 5,
             2 ^ 128 - 1, 2 ^ 128 + 2 ^ 64 + 7, 2 ^ 200 + 12345, 3 ^ 500].map (· + base)
  let mut h := 0
  for w in ws do
    for x in xs do
      let a := modPow x w
      let b := modShl x w
      let c := ofNatW w x
      h := (h * 31 + a + 7 * b + 11 * c) % 1000000007
      if a != b || a != c then IO.println s!"MISMATCH {x} {w}"
      -- `x` again (it was shared in the calls above).
      h := (h + x % 1000003) % 1000000007
    IO.println s!"w={w}: h={h} {modPow (3 ^ 500 + base) w % 1000000007} {modPow (2 ^ 64 + 5 + base) w}"
  for x in xs do
    IO.println s!"{mod64 x} {mod128 x} {mod63 x} {mod62 x}"
  -- Unique operands, truncated in their blocks.
  for k in [0, 1, 2, 7] do
    let w := 64 * k + 37 + base
    IO.println s!"fresh {k}: {modPow (fresh k) w} {modShl (fresh (k + 1)) (w + 64)} {ofNatW (w + 1) (fresh k)}"
  -- `BitVec` operations at widths from the command line.
  for w in [1, 8, 63, 64, 65, 100, 128, 130].map (· + base) do
    let x := 2 ^ (w + 3) + 2 ^ (w / 2) + 12345
    IO.println s!"bv {w}: {addW w x (2 ^ w - 1)} {mulW w x x} {shlW w x (w / 3)} {ofNatW w (2 ^ w)} {ofNatW w (2 ^ w - 1)}"
  -- lean-regex's bit set: every bit of a 3000-bit vector, set one by one.
  let n := 3000 + base
  let mut bv : BitVec n := 0#n
  for i in [0:n:7] do
    bv := setBit bv i
  IO.println s!"setBit {bv.toNat % 1000000007} {bv.toNat.log2} {(setBit bv (n + 5)).toNat == bv.toNat}"
  IO.println s!"lit {(add64 (BitVec.ofNat 64 (2 ^ 64 - 1)) 3).toNat} {(mul128 (BitVec.ofNat 128 (2 ^ 127 + 1)) 6).toNat}"
