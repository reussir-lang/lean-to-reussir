/-
lean2rr classic corpus: `mergesort` (written for this corpus).

One polymorphic, stable, top-down merge sort over `List α` with `[Ord α]`,
used at `Nat`, `Int`, `String`, `UInt64`, a user structure with a derived
`Ord` instance, and a user structure with a hand-written `Ord` instance
that compares only a key (to check stability). Every result is checked to
be sorted and to be a permutation of the input.

Size argument n (default 300000): the length of each list.
-/

/-- Split into two halves of (almost) equal length, preserving order:
  `splitAt` with an accumulator (tail recursive). -/
def splitHalf {α : Type} (xs : List α) : List α × List α :=
  let rec go : Nat → List α → List α → List α × List α
    | 0,     acc, rest    => (acc.reverse, rest)
    | _ + 1, acc, []      => (acc.reverse, [])
    | k + 1, acc, y :: ys => go k (y :: acc) ys
  go (xs.length / 2) [] xs

/-- Stable merge: on ties the element from the left list comes first.
  Tail recursive with an accumulator. -/
def merge {α : Type} [Ord α] (xs ys : List α) : List α :=
  let rec go : List α → List α → List α → List α
    | [],      ys,      acc => acc.reverseAux ys
    | xs,      [],      acc => acc.reverseAux xs
    | x :: xs, y :: ys, acc =>
      if compare y x == .lt then go (x :: xs) ys (y :: acc)
      else go xs (y :: ys) (x :: acc)
  go xs ys []

/-- Top-down merge sort (`partial`: termination relies on `splitHalf`
  returning two strictly shorter halves when the length is at least 2). -/
partial def mergeSort {α : Type} [Ord α] (xs : List α) : List α :=
  match xs with
  | [] | [_] => xs
  | _ =>
    let (l, r) := splitHalf xs
    merge (mergeSort l) (mergeSort r)

def isSorted {α : Type} [Ord α] : List α → Bool
  | x :: y :: rest => compare x y != .gt && isSorted (y :: rest)
  | _ => true

/-- Insertion into a sorted list (for the small reference sort). -/
def insertSorted {α : Type} [Ord α] (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if compare x y == .gt then y :: insertSorted x ys else x :: y :: ys

/-! ## Deterministic data -/

def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

def randoms (n : Nat) (seed : UInt64) : List UInt64 := Id.run do
  let mut s := seed
  let mut out := []
  for _ in [0:n] do
    s := lcg s
    out := (s >>> 33) :: out
  return out

structure Person where
  name : String
  age : Nat
  score : Int
deriving Ord, BEq, Repr

instance : ToString Person := ⟨fun p => s!"{p.name}/{p.age}/{p.score}"⟩

/-- A record ordered only by `key`; `tag` records the original position. -/
structure Keyed where
  key : Nat
  tag : Nat

instance : Ord Keyed := ⟨fun a b => compare a.key b.key⟩

def syllables : Array String := #["ka", "lo", "mi", "ne", "ru", "so", "ta", "vé", "zu", "ß"]

def mkName (r : UInt64) : String :=
  let r := r.toNat
  syllables[r % 10]! ++ syllables[(r / 10) % 10]! ++ syllables[(r / 100) % 10]!

/-! ## Checks -/

/-- Order-independent fingerprint for permutation checks. -/
def bagHash (hs : List UInt64) : UInt64 × UInt64 :=
  hs.foldl (fun (a, b) h => (a + h, b ^^^ (h * 0x9E3779B97F4A7C15))) (0, 0)

/-- Order-dependent fingerprint of the sorted result. -/
def seqHash (hs : List UInt64) : UInt64 :=
  hs.foldl (fun acc h => acc * 1099511628211 + h) 14695981039346656037

def report {α : Type} [Ord α] (label : String) (xs : List α) (h : α → UInt64) (fmt : α → String) : IO Unit := do
  let ys := mergeSort xs
  let perm := bagHash (xs.map h) == bagHash (ys.map h) && xs.length == ys.length
  let first := ys.head?.map fmt |>.getD "-"
  let last := ys.getLast?.map fmt |>.getD "-"
  IO.println s!"{label}: n={ys.length} sorted={isSorted ys} perm={perm} first={first} last={last} hash={seqHash (ys.map h)}"

def main (args : List String) : IO UInt32 := do
  let n := (args.head?.bind String.toNat?).getD 300000
  let rs := randoms n 42

  let nats : List Nat := rs.map (·.toNat % 1000000)
  report "Nat" nats (·.toUInt64) toString

  let ints : List Int := rs.map fun r => (r.toNat % 2000001 : Int) - 1000000
  report "Int" ints (fun i => i.toInt64.toUInt64) toString

  let strs : List String := rs.map mkName
  report "String" strs String.hash id

  report "UInt64" rs id toString

  let people : List Person := rs.map fun (r : UInt64) =>
    { name := mkName (r >>> 7), age := (r % 90).toNat, score := (r.toNat % 1001 : Int) - 500 }
  report "Person" people (fun p => p.name.hash + p.age.toUInt64 * 31 + p.score.toInt64.toUInt64 * 1000003) toString

  -- Stability: many equal keys; the tags of equal keys must stay increasing.
  let keyed : List Keyed := (rs.zip (List.range n)).map fun (r, i) => { key := (r % 100).toNat, tag := i }
  let sortedK := mergeSort keyed
  let rec stable : List Keyed → Bool
    | a :: b :: rest => (a.key < b.key || (a.key == b.key && a.tag < b.tag)) && stable (b :: rest)
    | _ => true
  IO.println s!"Keyed: n={sortedK.length} sorted={isSorted sortedK} stable={stable sortedK} tagHash={seqHash (sortedK.map (·.tag.toUInt64))}"

  -- Small cross-check against insertion sort, and edge cases.
  let small := (rs.take 300).map (·.toNat % 50)
  let ins := small.foldl (fun acc x => insertSorted x acc) []
  IO.println s!"small: agree={mergeSort small == ins} empty={(mergeSort ([] : List Nat)).length} one={mergeSort [7]} rev={mergeSort (List.range 12).reverse} dups={mergeSort [3, 1, 3, 1, 2]} strs={mergeSort ["b", "é", "a", "B", "", "ab"]}"
  pure 0
