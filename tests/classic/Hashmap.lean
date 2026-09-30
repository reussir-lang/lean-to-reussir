import Std.Data.HashMap
import Std.Data.HashSet

/-
lean2rr classic corpus: `hashmap` (written for this corpus).

`Std.HashMap` and `Std.HashSet`: bulk insertion of many keys (with
overwrites), lookups that hit and miss, erasure, `alter`/`modify`,
`insertIfNew`, `fold`/`for` iteration, `size`, keys that are `Nat`,
`String` and a user structure with derived `Hashable`/`BEq`, and word
counting. Every count is checked against a value computed independently.

Size argument n (default 4000000): the number of keys.
-/

open Std

structure Point where
  x : Int
  y : Int
deriving BEq, Hashable, Repr

/-- A bijection on [0, n) when `gcd(a, n) = 1`: `i ↦ (a * i + b) % n`. -/
def perm (a b n i : Nat) : Nat := (a * i + b) % n

def check (b : Bool) : String := if b then "ok" else "FAIL"

def main (args : List String) : IO UInt32 := do
  let n := (args.head?.bind String.toNat?).getD 4000000
  let n := max n 10
  -- keys k = perm i are a permutation of [0, n) (7919 is prime and does not divide n
  -- unless n is a multiple of 7919; then use 7907)
  let a := if n % 7919 == 0 then 7907 else 7919

  -- 1. Insert n keys (value = 3k + 1), then overwrite every third key.
  let mut m : HashMap Nat Nat := {}
  for i in [0:n] do
    let k := perm a 12345 n i
    m := m.insert k (3 * k + 1)
  for i in [0:n:3] do
    m := m.insert i (2 * i)
  let overwritten := (n + 2) / 3
  -- expected sum of values: sum over k of (3k+1), with k ≡ 0 mod 3 replaced by 2k
  let mut expected := 0
  for k in [0:n] do
    expected := expected + (if k % 3 == 0 then 2 * k else 3 * k + 1)
  let total := m.fold (fun acc _ v => acc + v) 0
  IO.println s!"insert: size={m.size} (n={n}) sum={total} {check (total == expected && m.size == n)} overwritten={overwritten}"

  -- 2. Lookups: hits on every key, misses on [n, 2n).
  let mut hits := 0
  let mut hitSum := 0
  let mut misses := 0
  for k in [0:2 * n] do
    match m[k]? with
    | some v => hits := hits + 1; hitSum := hitSum + v
    | none => misses := misses + 1
  IO.println s!"lookup: hits={hits} misses={misses} {check (hits == n && misses == n && hitSum == expected)} contains={m.contains (n / 2)} {m.contains (n + 7)} getD={m.getD (n + 1) 77} get!={m.get! 3}"

  -- 3. Erase every key divisible by 5 (in a scrambled order), modify the rest.
  for i in [0:n] do
    let k := perm a 999 n i
    if k % 5 == 0 then m := m.erase k
  let erased := (n + 4) / 5
  m := m.modify 1 (· + 1000000)
  m := m.alter 2 (fun | some v => some (v * 10) | none => some 0)
  m := m.alter 5 (fun | some v => some v | none => some 555)     -- 5 was erased: re-inserted
  m := m.alter 7 (fun _ => none)                                -- deletes 7
  m := m.insertIfNew 1 0                                        -- 1 exists: unchanged
  m := m.insertIfNew (n + 3) 42                                 -- new key
  -- erased multiples of 5, then +1 (key 5 re-inserted), -1 (key 7 deleted), +1 (key n+3)
  let expectedSize := n - erased + 1 - 1 + 1
  IO.println s!"erase: size={m.size} {check (m.size == expectedSize)} v1={m[1]?} v2={m[2]?} v5={m[5]?} v7={m[7]?} vnew={m[n + 3]?} v10={m[10]?}"

  -- 4. Iterate with `for`, and check keys/values against the rule.
  let mut bad := 0
  let mut keySum := 0
  let mut orderHash : UInt64 := 0   -- depends on the iteration order
  for (k, v) in m do
    keySum := keySum + k
    orderHash := orderHash * 1000003 + k.toUInt64
    let want :=
      if k == 1 then 3 * 1 + 1 + 1000000
      else if k == 2 then (3 * 2 + 1) * 10
      else if k == 5 then 555
      else if k == n + 3 then 42
      else if k % 3 == 0 then 2 * k
      else 3 * k + 1
    if v != want then bad := bad + 1
  IO.println s!"iterate: keySum={keySum} bad={bad} {check (bad == 0)} orderHash={orderHash}"

  -- 5. String keys: word counts over a generated text.
  let vocab := #["the", "quick", "brown", "fox", "jumps", "over", "lazy", "dog", "λ", "ünïcode", "日本", ""]
  let mut counts : HashMap String Nat := {}
  let mut s : UInt64 := 7
  let words := n / 4
  let mut direct := Array.replicate vocab.size 0
  for _ in [0:words] do
    s := s * 6364136223846793005 + 1442695040888963407
    let j := ((s >>> 33) % vocab.size.toUInt64).toNat
    let w := vocab[j]!
    counts := counts.alter w (fun | some c => some (c + 1) | none => some 1)
    direct := direct.modify j (· + 1)
  let mut agree := true
  for h : j in [0:vocab.size] do
    if counts.getD vocab[j] 0 != direct[j]! then agree := false
  let sorted := counts.toList.toArray.qsort (fun p q => p.1 < q.1)
  IO.println s!"words: distinct={counts.size} total={counts.fold (fun acc _ c => acc + c) 0} agree={check agree} counts={sorted.toList}"

  -- 6. Structure keys and a HashSet.
  let mut grid : HashMap Point Nat := {}
  let side := Nat.sqrt (n / 4) + 1
  for x in [0:side] do
    for y in [0:side] do
      grid := grid.insert ⟨x - side / 2, (y : Int) * 3 - 5⟩ (x * side + y)
  let probe := grid.get? ⟨0, -5⟩
  let mut set : HashSet Nat := {}
  for i in [0:n] do
    set := set.insert ((i * i) % 1000003)
  let mut qr := 0
  for i in [0:1000003] do
    if set.contains i then qr := qr + 1
  IO.println s!"struct keys: size={grid.size} {check (grid.size == side * side)} probe={probe} set={set.size} qr={qr} {check (qr == set.size)} gridOrder={grid.fold (fun (acc : UInt64) _ v => acc * 31 + v.toUInt64) 0}"
  pure 0
