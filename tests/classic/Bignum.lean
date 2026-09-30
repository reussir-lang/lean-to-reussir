/-
lean2rr classic corpus: `bignum` (written for this corpus).

Arbitrary-precision `Nat` and `Int` far past 2^64: Fibonacci numbers and
factorials computed two different ways and cross-checked, identities that
mix `Int` signs, the three `Int` division conventions, bit operations,
decimal conversion both ways, and arithmetic right at the boundaries where
Lean switches between scalar and heap (GMP) representations (2^63, 2^64).

Size argument n (default 6000): Fibonacci uses index 10n, factorials use n.
-/

/-! ## Fibonacci -/

/-- Iterative Fibonacci: `fibLoop k a b = F(i + k)` when `a = F(i)`, `b = F(i+1)`. -/
def fibLoop : Nat → Nat → Nat → Nat
  | 0,     a, _ => a
  | k + 1, a, b => fibLoop k b (a + b)

def fibIter (n : Nat) : Nat := fibLoop n 0 1

/-- Fast doubling: returns `(F(n), F(n+1))`.
  F(2k) = F(k) * (2 F(k+1) - F(k)),  F(2k+1) = F(k)^2 + F(k+1)^2. -/
def fibPair (n : Nat) : Nat × Nat :=
  if h : n = 0 then (0, 1)
  else
    have : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
    let (a, b) := fibPair (n / 2)
    let c := a * (2 * b - a)
    let d := a * a + b * b
    if n % 2 == 0 then (c, d) else (d, c + d)
termination_by n

def fibFast (n : Nat) : Nat := (fibPair n).1

/-- Fibonacci numbers for negative indices, by stepping backwards:
  F(k-1) = F(k+1) - F(k). Returns F(-n). -/
def fibNeg (n : Nat) : Int := Id.run do
  let mut hi : Int := 1   -- F(1)
  let mut lo : Int := 0   -- F(0)
  for _ in [0:n] do
    let next := hi - lo   -- F(k-1) from F(k+1) = hi and F(k) = lo
    hi := lo
    lo := next
  return lo

/-! ## Factorials -/

def factIter (n : Nat) : Nat := Id.run do
  let mut acc := 1
  for i in [1:n+1] do
    acc := acc * i
  return acc

/-- Product of `lo * (lo+1) * ... * (hi-1)` by divide and conquer. -/
def prodRange (lo hi : Nat) : Nat :=
  if h : hi ≤ lo + 1 then (if lo < hi then lo else 1)
  else
    let mid := (lo + hi) / 2
    have : mid - lo < hi - lo := by omega
    have : hi - mid < hi - lo := by omega
    prodRange lo mid * prodRange mid hi
termination_by hi - lo

def factTree (n : Nat) : Nat := prodRange 1 (n + 1)

/-- Legendre: the exponent of `p` in `n!`. -/
def legendre (n p : Nat) : Nat :=
  if h : p ≤ 1 ∨ n < p then 0
  else
    have : n / p < n := Nat.div_lt_self (by omega) (by omega)
    n / p + legendre (n / p) p
termination_by n

def trailingZeros (s : String) : Nat :=
  (s.toList.reverse.takeWhile (· == '0')).length

/-! ## Helpers -/

def digitSum (s : String) : Nat :=
  s.foldl (fun acc c => acc + (c.toNat - '0'.toNat)) 0

def popCount (n : Nat) : Nat := Id.run do
  let mut k := n
  let mut c := 0
  while k != 0 do
    c := c + k % 2
    k := k / 2
  return c

def powMod (b e m : Nat) : Nat := Id.run do
  let mut result := 1 % m
  let mut base := b % m
  let mut exp := e
  while exp > 0 do
    if exp % 2 == 1 then
      result := result * base % m
    base := base * base % m
    exp := exp / 2
  return result

/-- Newton's method integer square root. -/
partial def isqrt (x : Nat) : Nat :=
  if x < 2 then x
  else
    let rec go (r : Nat) : Nat :=
      let r' := (r + x / r) / 2
      if r' >= r then r else go r'
    go x

def summary (x : Nat) : String :=
  let s := toString x
  s!"digits={s.length} digitsum={digitSum s} head={(s.take 12).toString} last={(s.takeEnd 12).toString} mod1e9+7={x % 1000000007}"

def check (b : Bool) : String := if b then "ok" else "FAIL"

/-! ## Int division conventions on a sign grid -/

def divGrid (as bs : List Int) : String := Id.run do
  let mut parts : Array String := #[]
  for a in as do
    for b in bs do
      parts := parts.push s!"{a}/{b}: e={a / b},{a % b} t={a.tdiv b},{a.tmod b} f={a.fdiv b},{a.fmod b}"
  return ", ".intercalate parts.toList

def divIdentities (as bs : List Int) : Bool := Id.run do
  for a in as do
    for b in bs do
      if b != 0 then
        if a / b * b + a % b != a then return false
        if a.tdiv b * b + a.tmod b != a then return false
        if a.fdiv b * b + a.fmod b != a then return false
        if (a % b) < 0 then return false
        if (a % b).natAbs >= b.natAbs then return false
  return true

def main (args : List String) : IO UInt32 := do
  let n := (args.head?.bind String.toNat?).getD 6000
  let fn := 10 * n

  -- Fibonacci, two ways, plus identities
  let f1 := fibIter fn
  let f2 := fibFast fn
  IO.println s!"fib({fn}): {summary f1}"
  let fm1 := fibIter (fn - 1)
  let fp1 := fibIter (fn + 1)
  let cassini : Int := (fm1 : Int) * fp1 - (f1 : Int) * f1
  let sign : Int := if fn % 2 == 0 then 1 else -1
  let neg := fibNeg fn
  let negOk := neg == (if fn % 2 == 0 then -(f1 : Int) else (f1 : Int))
  let g := Nat.gcd (fibIter (6 * n)) (fibIter (4 * n))
  let gcdOk := g == fibIter (Nat.gcd (6 * n) (4 * n))
  IO.println s!"fib checks: iter=fast {check (f1 == f2)}, cassini {check (cassini == sign)}, negative index {check negOk}, gcd {check gcdOk}, F(-{fn}) sign {neg.sign}"

  -- Factorials, two ways
  let n1 := factIter n
  let n2 := factTree n
  let s := toString n1
  let tz := trailingZeros s
  IO.println s!"{n}!: {summary n1}"
  IO.println s!"fact checks: iter=tree {check (n1 == n2)}, trailing zeros {tz} = legendre {legendre n 5} {check (tz == legendre n 5)}, roundtrip {check (s.toNat? == some n1)}, (n!)/((n-1)!) {check (n1 / factIter (n - 1) == n)}"

  -- Mixed-sign big Int arithmetic
  let a : Int := -(f1 : Int) + 12345
  let b : Int := (fibIter (fn / 3) : Int) + 7
  let q := a / b
  let r := a % b
  IO.println s!"int: a/b digits={(toString q).length} a%b mod1e9+7={r % 1000000007} tdiv={(a.tdiv b) % 1000003} fdiv={(a.fdiv b) % 1000003} gcd={(Int.gcd a b) % 1000000007} ids {check (divIdentities [a, -a, a + 1, 0] [b, -b, 3, -3, 1])}"

  -- Division conventions on small values and around 2^64
  IO.println s!"grid: {divGrid [7, -7] [2, -2]}"
  let big : Int := 2^100 + 7
  let den : Int := 2^64 + 3
  IO.println s!"grid big: {divGrid [big, -big] [den, -den]}"

  -- Scalar / heap boundaries
  let m63 : Nat := 2^63
  let m64 : Nat := 2^64
  IO.println s!"boundary: {m63 - 1 + 1} {m63 * 2 - 1} {m64 + m64} {(m64 - 1) * (m64 - 1)} {m64 * m64 / (m64 - 1)} {m64 * m64 % (m64 - 1)} {(5 : Nat) - m64} {m64 - m63 - m63} {(m64 + 5).toUInt64} {(m64 - 1).toUInt64 + 1} {(-(m64 : Int) - 1).toNat} {(-(m64 : Int) - 1).natAbs}"
  let im63 : Int := -(2^63 : Int)
  IO.println s!"int boundary: {im63 - 1} {im63 + 1} {-im63} {im63 * im63} {im63 / (-1)} {im63 % 7} {(im63 - 1).tdiv 2} {Int.toNat (im63 * -2)}"

  -- Bits, powers, roots
  let x := f1 * f1 + 1
  IO.println s!"bits: log2={Nat.log2 f1} popcount={popCount f1} testBit={f1.testBit 100} shl/shr {check ((f1 <<< 777) >>> 777 == f1)} and={(f1 &&& (m64 - 1))} or={(f1 ||| 1) % 1000000007} xor={(f1 ^^^ fp1) % 1000000007} ashr={(-(f1 : Int)) >>> 1000 % 1000000007}"
  let r := isqrt x
  IO.println s!"pow/sqrt: 3^{n} mod p {check ((3 ^ n) % 1000000007 == powMod 3 n 1000000007)} {powMod 3 n 1000000007} isqrt {check (r == f1)} Nat.sqrt {check (Nat.sqrt x == f1)} 2^{fn} digits={(toString (2 ^ fn)).length}"

  -- Known values (checked against an independent implementation)
  IO.println s!"known: F(300)={fibFast 300} 50!={factTree 50} F(-301)={fibNeg 301} lcm={Nat.lcm (2^70 - 1) (2^42 - 1)}"
  pure 0
