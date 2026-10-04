/-! Runtime test: CSLib's cost-counting monad `TimeM` and its insertion sort
over any monad. `TimeM T α` is a structure of a result and a cost of type
`T`, with its own `Pure`, `Bind`, `Functor`, `Seq`, `SeqLeft`, `SeqRight`
and `Monad` instances, `tick`, and the `✓`/`✓[c]` do-element macros.
`List.orderedInsertM` and `List.insertionSortM` take a comparator
`α → α → m Bool` in any monad `m`. The program sorts at `Id`, at `TimeM ℕ`
(comparisons counted by `tick` and by `✓`; sorted, reversed and empty
inputs), at `TimeM ℤ` (negative costs), at `StateM` (a counter), at
`Option` and `Except` (a comparator that fails) and at `IO` (a comparator
that prints); on `Nat`, `Int`, `String` and pairs (stability). It checks
the results against Mathlib's `List.insertionSort` and core's
`List.mergeSort`, and sorts 2000 numbers. Arguments: a seed and a length.
A coverage test from CSLib (github.com/leanprover/cslib, commit 990e65a),
a library of computer science formalized in Lean: its computational code
only, proofs dropped, in one program that imports only Init. (A program
that imports CSLib imports Mathlib, which lean2rr does not support: plan
§10, "Not supported".) Mathlib code is from v4.34.0 (5ed2965), the version
CSLib 990e65a pins.
It draws on CSLib's Cslib/Algorithms/Lean/TimeM.lean and
Cslib/Algorithms/Lean/Sort/Insertion.lean, and copies Mathlib's `AddZero`
class and `List.orderedInsert`/`List.insertionSort`. `lcg`, `genList`, the
comparators and `main` are not CSLib code: they are the round-9 driver,
whose output on the real CSLib is the same as this program's.
From the round-9 review, area cslib (rv9/cslib), program CslxInsertion.

Copyright notices of the copied code. It is used under the Apache License,
Version 2.0 (the file LICENSE of CSLib and of Mathlib;
http://www.apache.org/licenses/LICENSE-2.0) and changed here: the proofs
are removed and the Mathlib dependencies are replaced as described above.
* CSLib, Cslib/Algorithms/Lean/TimeM.lean:
    Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Sorrachai Yingchareonthawornhcai, Eric Wieser
* CSLib, Cslib/Algorithms/Lean/Sort/Insertion.lean:
    Copyright (c) 2016 Jeremy Avigad. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Jeremy Avigad, Eric Wieser
* Mathlib, Mathlib/Algebra/Group/Monoid.lean (`AddZero`):
    Copyright (c) 2014 Jeremy Avigad. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
* Mathlib, Mathlib/Data/List/Sort.lean (`orderedInsert`, `insertionSort`):
    Copyright (c) 2016 Jeremy Avigad. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Jeremy Avigad, Wrenna Robson
-/

/-! ### Extract of `Cslib/Algorithms/Lean/TimeM.lean` (CSLib 990e65a), code only.
`AddZero` is Mathlib's class (`Mathlib/Algebra/Group/Monoid.lean`), copied. -/

notation "ℕ" => Nat
notation "ℤ" => Int

class AddZero (M : Type u) extends Zero M, Add M

instance : AddZero Nat := {}
instance : AddZero Int := {}

namespace Cslib.Algorithms.Lean

structure TimeM (T : Type u) (α : Type v) where
  ret : α
  time : T

namespace TimeM

protected def pure [Zero T] {α} (a : α) : TimeM T α :=
  ⟨a, 0⟩

instance [Zero T] : Pure (TimeM T) where
  pure := TimeM.pure

protected def bind {α β} [Add T] (m : TimeM T α) (f : α → TimeM T β) : TimeM T β :=
  let r := f m.ret
  ⟨r.ret, m.time + r.time⟩

instance [Add T] : Bind (TimeM T) where
  bind := TimeM.bind

instance : Functor (TimeM T) where
  map f x := ⟨f x.ret, x.time⟩

instance [Add T] : Seq (TimeM T) where
  seq f x := ⟨f.ret (x ()).ret, f.time + (x ()).time⟩

instance [Add T] : SeqLeft (TimeM T) where
  seqLeft x y := ⟨x.ret, x.time + (y ()).time⟩

instance [Add T] : SeqRight (TimeM T) where
  seqRight x y := ⟨(y ()).ret, x.time + (y ()).time⟩

instance [AddZero T] : Monad (TimeM T) where
  pure := Pure.pure
  bind := Bind.bind
  map := Functor.map
  seq := Seq.seq
  seqLeft := SeqLeft.seqLeft
  seqRight := SeqRight.seqRight

def tick (c : T) : TimeM T PUnit := ⟨.unit, c⟩

macro "✓[" c:term "]" body:doElem : doElem => `(doElem| do TimeM.tick $c; $body:doElem)

macro "✓" body:doElem : doElem => `(doElem| ✓[1] $body)

end TimeM
end Cslib.Algorithms.Lean

/-! ### Mathlib `Mathlib/Data/List/Sort.lean` (code) -/
namespace List
section
variable {α : Type u} (r : α → α → Prop) [DecidableRel r]
def orderedInsert (a : α) : List α → List α
  | [] => [a]
  | b :: l => if r a b then a :: b :: l else b :: orderedInsert a l
def insertionSort : List α → List α := foldr (orderedInsert r) []
end

/-! ### CSLib `Cslib/Algorithms/Lean/Sort/Insertion.lean` (code) -/
variable {m n} [Monad m] [Monad n] (r : α → α → m Bool)

def orderedInsertM (a : α) : List α → m (List α)
  | [] => return [a]
  | b :: l => do if ← r a b then return a :: b :: l else return b :: (← orderedInsertM a l)

def insertionSortM : List α → m (List α)
  | [] => return []
  | b :: l => do orderedInsertM r b (← insertionSortM l)
end List

open Cslib.Algorithms.Lean

def lcg (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

def genList (seed n m : Nat) : List Nat := Id.run do
  let mut s := seed
  let mut acc := []
  for _ in [0:n] do
    s := lcg s
    acc := (s / 7 % m) :: acc
  return acc

def leId (x y : Nat) : Id Bool := pure (decide (x ≤ y))
def leTime (x y : Nat) : TimeM ℕ Bool := do TimeM.tick 1; return decide (x ≤ y)
def leTick (x y : Nat) : TimeM ℕ Bool := do ✓ return decide (x ≤ y)
def leState (x y : Nat) : StateM Nat Bool := do modify (· + 1); return decide (x ≤ y)
def leOpt (bad : Nat) (x y : Nat) : Option Bool :=
  if x == bad || y == bad then none else some (decide (x ≤ y))
def leExc (bad : Nat) (x y : Nat) : Except String Bool :=
  if x == bad then throw s!"refused to compare {x} with {y}" else pure (decide (x ≤ y))
def leIO (x y : Nat) : IO Bool := do
  if x == y then IO.println s!"  io: tie {x}"
  return decide (x ≤ y)

def showOpt : Option (List Nat) → String
  | none => "none"
  | some l => s!"some {l}"

def showExc : Except String (List Nat) → String
  | .error e => s!"error {e}"
  | .ok l => s!"ok {l}"

def main (args : List String) : IO Unit := do
  let seed := (args.head? >>= String.toNat?).getD 42
  let n := ((args.drop 1).head? >>= String.toNat?).getD 12
  let xs := genList seed n 50
  IO.println s!"input: {xs}"
  -- Id
  let s1 := Id.run (List.insertionSortM leId xs)
  IO.println s!"Id sorted: {s1}"
  IO.println s!"matches List.insertionSort: {s1 == List.insertionSort (· ≤ ·) xs}"
  IO.println s!"descending: {Id.run (List.insertionSortM (fun x y => pure (decide (y ≤ x))) xs)}"
  -- orderedInsertM
  IO.println s!"orderedInsertM 25: {Id.run (List.orderedInsertM leId 25 s1)}"
  IO.println s!"orderedInsertM into []: {Id.run (List.orderedInsertM leId 7 [])}"
  -- TimeM ℕ: comparisons
  let t := List.insertionSortM leTime xs
  IO.println s!"TimeM ret: {t.ret} time: {t.time}"
  let t2 := List.insertionSortM leTick xs
  IO.println s!"TimeM(✓) ret==: {t2.ret == t.ret} time: {t2.time}"
  let tsorted := List.insertionSortM leTime s1
  IO.println s!"TimeM on sorted input: time {tsorted.time}"
  let trev := List.insertionSortM leTime s1.reverse
  IO.println s!"TimeM on reversed input: time {trev.time}"
  let tn := List.insertionSortM leTime ([] : List Nat)
  IO.println s!"TimeM on []: {tn.ret} time {tn.time}"
  -- TimeM ℤ cost (negative ticks)
  let tz : TimeM ℤ (List Nat) := List.insertionSortM (fun x y => do TimeM.tick (-2 : ℤ); return decide (x ≤ y)) xs
  IO.println s!"TimeM Int cost: {tz.time}"
  -- StateM: comparison counter
  let (s3, cnt) := (List.insertionSortM leState xs).run 0
  IO.println s!"StateM sorted==: {s3 == s1} count: {cnt}"
  -- Option
  let bad := xs.getD 3 0
  IO.println s!"Option ok: {showOpt (List.insertionSortM (leOpt 1000) xs)}"
  IO.println s!"Option bad {bad}: {showOpt (List.insertionSortM (leOpt bad) xs)}"
  -- Except
  IO.println s!"Except ok: {showExc (List.insertionSortM (leExc 1000) xs)}"
  IO.println s!"Except bad: {showExc (List.insertionSortM (leExc bad) xs)}"
  -- IO comparator
  let s4 ← List.insertionSortM leIO (xs.take 8 ++ xs.take 2)
  IO.println s!"IO sorted: {s4}"
  -- Int and String
  let zs : List Int := xs.map (fun (x : Nat) => (x : Int) - 25)
  IO.println s!"Int sorted: {Id.run (List.insertionSortM (fun x y => pure (decide (x ≤ y))) zs)}"
  let ws : List String := xs.map (fun x => s!"w{x % 13}{String.ofList (List.replicate (x % 3) 'z')}")
  IO.println s!"String sorted: {Id.run (List.insertionSortM (fun x y => pure (decide (x ≤ y))) ws)}"
  -- stability on pairs, key only
  let ps := xs.zip (List.range xs.length) |>.map (fun (a, i) => (a % 5, i))
  let sp := Id.run (List.insertionSortM (fun a b => pure (decide (a.1 ≤ b.1))) ps)
  IO.println s!"pairs by key: {sp}"
  -- a larger run
  let big := genList (seed + 1) 2000 100000
  let tb := List.insertionSortM leTime big
  IO.println s!"big: len {tb.ret.length} sum {tb.ret.foldl (· + ·) 0} head {tb.ret.head?} last {tb.ret.getLast?} time {tb.time}"
  IO.println s!"big sorted ok: {tb.ret == List.mergeSort big}"
