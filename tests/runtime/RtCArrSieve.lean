/-! Runtime test (compact scalar arrays, plan "Why" and "Tests": the RSS
check for sieve): the sieve of Eratosthenes over an `Array Bool` of
n + 1 elements, updated in place by `set!`, then counted by `foldl`; also
the last prime up to n and a checksum of the primes below 10^5 (an
`Array UInt32` made by `filterMap`). Natively the `Array Bool` is n boxed
words (the classic sieve's 485 MB at n = 5 * 10^7); with compact arrays
it is n bytes. `RtCArrSieve.alloc` runs n = 5 * 10^6 and 5 * 10^7 and
bounds lean2rr's peak memory at n = 5 * 10^7 by 120000 KB (the compact
array is 48828 KB; the boxed one 390625 KB). Argument: n (default
5 * 10^7; pi(5 * 10^7) = 3001134). -/

@[noinline] def sieve (n : Nat) : Array Bool := Id.run do
  let mut isPrime := (Array.replicate (n + 1) true).set! 0 false |>.set! 1 false
  let mut i := 2
  while i * i ≤ n do
    if isPrime[i]! then
      let mut j := i * i
      while j ≤ n do
        isPrime := isPrime.set! j false
        j := j + i
    i := i + 1
  return isPrime

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 50000000
  let s := sieve n
  let count := s.foldl (fun c b => if b then c + 1 else c) 0
  let last := Id.run do
    let mut k := n
    while k > 0 && !s[k]! do
      k := k - 1
    return k
  let small : Array UInt32 := (s.extract 0 (min (n + 1) 100000)).zipIdx.filterMap fun (b, i) =>
    if b then some i.toUInt32 else none
  let sum := small.foldl (fun h p => (h ^^^ p.toUInt64) * 1099511628211) 7
  IO.println s!"{n} {count} {last} {small.size} {sum}"
