/-
lean2rr classic corpus: `sieve` (written for this corpus).

Sieve of Eratosthenes over `Array Bool` with `for` loops over ranges
(including stepped ranges and `break`/`continue`), a smallest-prime-factor
sieve over `Array Nat`, and cross-checks against trial division and the
known values of the prime-counting function.

Size argument n (default 50000000): the sieve limit.
-/

/-- `isPrime[i]` for all `i < n`. -/
def sieve (n : Nat) : Array Bool := Id.run do
  let mut a := Array.replicate n true
  if n > 0 then a := a.set! 0 false
  if n > 1 then a := a.set! 1 false
  for i in [2:n] do
    if i * i ≥ n then break
    if !a[i]! then continue
    if hpos : 0 < i then
      -- the stepped range `[i*i : n : i]`, with the step's positivity proof
      for j in ({ start := i * i, stop := n, step := i, step_pos := hpos } : Std.Legacy.Range) do
        a := a.set! j false
  return a

/-- Smallest prime factor of every `i < n` (0 and 1 map to themselves). -/
def spfSieve (n : Nat) : Array Nat := Id.run do
  let mut spf := Array.range n
  let mut i := 2
  while i * i < n do
    if spf[i]! == i then
      let mut j := i * i
      while j < n do
        if spf[j]! == j then
          spf := spf.set! j i
        j := j + i
    i := i + 1
  return spf

def isPrimeTrial (k : Nat) : Bool := Id.run do
  if k < 2 then return false
  let mut d := 2
  while d * d ≤ k do
    if k % d == 0 then return false
    d := d + 1
  return true

/-- Number of prime factors of `k` counted with multiplicity, via `spf`. -/
partial def omega (spf : Array Nat) (k : Nat) (acc : Nat := 0) : Nat :=
  if k < 2 then acc else omega spf (k / spf[k]!) (acc + 1)

def main (args : List String) : IO UInt32 := do
  let n := (args.head?.bind String.toNat?).getD 50000000
  let isP := sieve n

  -- Summary of the Boolean sieve.
  let mut count := 0
  let mut sum := 0
  let mut last := 0
  let mut twins := 0
  let mut maxGap := 0
  let mut prev := 0
  for h : i in [0:isP.size] do
    if isP[i] then
      count := count + 1
      sum := sum + i
      if prev > 0 then
        if i - prev == 2 then twins := twins + 1
        if i - prev > maxGap then maxGap := i - prev
      prev := i
      last := i
  IO.println s!"primes below {n}: count={count} sum={sum} last={last} twins={twins} maxgap={maxGap}"

  -- pi(10^k) for every power of ten up to n, from the prefix counts.
  let mut pis : Array String := #[]
  let mut acc := 0
  let mut next := 10
  for i in [0:n+1] do
    if i == next then
      pis := pis.push s!"pi({i})={acc}"
      next := next * 10
    if i < n && isP[i]! then acc := acc + 1
  IO.println s!"{" ".intercalate pis.toList}"

  -- Cross-check the first primes and a window at the top with trial division.
  let mut mismatches := 0
  for k in [0:min n 20000] do
    if isP[k]! != isPrimeTrial k then mismatches := mismatches + 1
  for k in [n - min n 2000 : n] do
    if isP[k]! != isPrimeTrial k then mismatches := mismatches + 1
  IO.println s!"trial division mismatches: {mismatches}"

  -- Smallest-prime-factor sieve on a smaller range: agreement and Omega sums.
  let m := n / 4
  let spf := spfSieve m
  let mut agree := true
  let mut omegaSum := 0
  let mut spfSum := 0
  for k in [2:m] do
    if (spf[k]! == k) != isP[k]! then agree := false
    omegaSum := omegaSum + omega spf k
    spfSum := spfSum + spf[k]!
  IO.println s!"spf below {m}: agree={agree} omegaSum={omegaSum} spfSum={spfSum}"
  pure 0
