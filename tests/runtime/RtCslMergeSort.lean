/-! Runtime test: CSLib's merge sort over any monad and its comparison count.
`List.mergeM` and `List.mergeSortM` take a comparator `α → α → m Bool` in
any monad `m`; `mergeSortM` splits with core's
`MergeSort.Internal.splitInTwo` (a subtype argument) and recurses by
well-founded recursion (`termination_by`). `TimeM.merge` and
`TimeM.mergeSort` count the comparisons in the cost monad `TimeM ℕ`
(through the `✓` do-element macro) over a `LinearOrder`;
`timeMergeSortRec` is the recurrence and `T n = n * Nat.clog 2 n` the
bound, checked for lengths 0..39. The program sorts at `Id`, `TimeM`,
`StateM` (a counter), `Except` (a comparator that fails) and `IO` (a
comparator that prints, in order); on `Nat`, `Int`, `String` and pairs
(stability); checks the results against core's `List.mergeSort`; uses the
`TimeM` instances `pure`, `<$>`, `<*>`, `<*`, `*>` and `tick`; and sorts
5000 numbers. Arguments: a seed and a length.
A coverage test from CSLib (github.com/leanprover/cslib, commit 990e65a),
a library of computer science formalized in Lean: its computational code
only, proofs dropped, in one program that imports only Init. (A program
that imports CSLib imports Mathlib, which lean2rr does not support: plan
§10, "Not supported".) Mathlib code is from v4.34.0 (5ed2965), the version
CSLib 990e65a pins.
It draws on CSLib's Cslib/Algorithms/Lean/TimeM.lean,
Cslib/Algorithms/Lean/Sort/Merge.lean and
Cslib/Algorithms/Lean/MergeSort/MergeSort.lean, and copies Mathlib's
`AddZero` class and `Nat.clog`. `LinearOrder` is a new, minimal stand-in
for Mathlib's class: it holds only the decidable `≤`. `lcg`, `genList`,
the comparators and `main` are not CSLib code: they are the round-9
driver, whose output on the real CSLib is the same as this program's.
From the round-9 review, area cslib (rv9/cslib), program CslxMergeSort.

Copyright notices of the copied code. It is used under the Apache License,
Version 2.0 (the file LICENSE of CSLib and of Mathlib;
http://www.apache.org/licenses/LICENSE-2.0) and changed here: the proofs
are removed and the Mathlib dependencies are replaced as described above.
* CSLib, Cslib/Algorithms/Lean/TimeM.lean:
    Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Sorrachai Yingchareonthawornhcai, Eric Wieser
* CSLib, Cslib/Algorithms/Lean/Sort/Merge.lean:
    Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Kim Morrison, Eric Wieser
* CSLib, Cslib/Algorithms/Lean/MergeSort/MergeSort.lean:
    Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Sorrachai Yingchareonthawornhcai
* Mathlib, Mathlib/Algebra/Group/Monoid.lean (`AddZero`):
    Copyright (c) 2014 Jeremy Avigad. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
* Mathlib, Mathlib/Data/Nat/Log.lean (`Nat.clog`):
    Copyright (c) 2020 Simon Hudon. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Simon Hudon, Yaël Dillies, Yury Kudryashov
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

/-! ### Mathlib stand-ins -/
class LinearOrder (α : Type u) extends LE α where
  decidableLE : DecidableRel (α := α) (· ≤ ·)

instance (priority := 50) [LinearOrder α] : DecidableRel (α := α) (· ≤ ·) := LinearOrder.decidableLE
instance : LinearOrder Nat := { decidableLE := inferInstance }
instance : LinearOrder Int := { decidableLE := inferInstance }
instance : LinearOrder String := { decidableLE := inferInstance }

namespace Nat
/-- Mathlib `Mathlib/Data/Nat/Log.lean`, copied. -/
def clog (b n : ℕ) : ℕ :=
  if 1 < b ∧ 1 < n then (go b n).2 + 1 else 0 where
  go : ℕ → ℕ → ℕ × ℕ
  | b, 0 => (b / n, 0)
  | b, fuel + 1 =>
    if n ≤ b then (b / n, 0)
    else
      let (q, e) := go (b * b) fuel
      if q < b then (q, 2 * e + 1) else (q / b, 2 * e)
end Nat

/-! ### CSLib `Cslib/Algorithms/Lean/Sort/Merge.lean` (code) -/
namespace List

variable {m n} [Monad m] [Monad n]

def mergeM (xs ys : List α) (le : α → α → m Bool) : m (List α) := do
  match xs, ys with
  | [], ys => return ys
  | xs, [] => return xs
  | x :: xs, y :: ys =>
    if ← le x y then
      return x :: (← mergeM xs (y :: ys) le)
    else
      return y :: (← mergeM (x :: xs) ys le)

def mergeSortM (xs : List α) (le : α → α → m Bool) : m (List α) :=
  match xs with
  | [] => return []
  | [a] => return [a]
  | a :: b :: xs => do
    let lr := MergeSort.Internal.splitInTwo ⟨a :: b :: xs, rfl⟩
    mergeM (← mergeSortM lr.1 le) (← mergeSortM lr.2 le) le
termination_by xs.length

end List

/-! ### CSLib `Cslib/Algorithms/Lean/MergeSort/MergeSort.lean` (code) -/
set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

variable {α : Type}

variable [LinearOrder α]

abbrev merge (xs ys : List α) : TimeM ℕ (List α) :=
  List.mergeM xs ys fun x y => do ✓ return x ≤ y

abbrev mergeSort (xs : List α) : TimeM ℕ (List α) :=
  List.mergeSortM xs fun x y => do ✓ return x ≤ y

def timeMergeSortRec : ℕ → ℕ
| 0 => 0
| 1 => 0
| n@(_+2) => timeMergeSortRec (n/2) + timeMergeSortRec ((n-1)/2 + 1) + n

open Nat (clog)

abbrev T (n : ℕ) : ℕ := n * clog 2 n

end Cslib.Algorithms.Lean.TimeM

set_option autoImplicit true

open Cslib.Algorithms.Lean

def lcg (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

def genList (seed n m : Nat) : List Nat := Id.run do
  let mut s := seed
  let mut acc := []
  for _ in [0:n] do
    s := lcg s
    acc := (s / 7 % m) :: acc
  return acc

def leState (x y : Nat) : StateM Nat Bool := do modify (· + 1); return decide (x ≤ y)
def leExc (bad : Nat) (x y : Nat) : Except String Bool :=
  if y == bad then throw s!"cannot compare {x} and {y}" else pure (decide (x ≤ y))
def leIO (x y : Int) : IO Bool := do
  IO.println s!"  cmp {x} {y}"
  return decide (x ≤ y)

def showExc : Except String (List Nat) → String
  | .error e => s!"error {e}"
  | .ok l => s!"ok {l}"

def main (args : List String) : IO Unit := do
  let seed := (args.head? >>= String.toNat?).getD 7
  let n := ((args.drop 1).head? >>= String.toNat?).getD 13
  let xs := genList seed n 40
  let ys := genList (seed + 3) (n / 2) 40
  IO.println s!"xs: {xs}"
  IO.println s!"ys: {ys}"
  -- Id
  let sx := Id.run (List.mergeSortM xs (fun x y => pure (decide (x ≤ y))))
  let sy := Id.run (List.mergeSortM ys (fun x y => pure (decide (x ≤ y))))
  IO.println s!"Id mergeSortM xs: {sx}"
  IO.println s!"== List.mergeSort: {sx == List.mergeSort xs}"
  IO.println s!"Id mergeM: {Id.run (List.mergeM sx sy (fun x y => pure (decide (x ≤ y))))}"
  IO.println s!"mergeM [] ys: {Id.run (List.mergeM [] sy (fun x y => pure (decide (x ≤ y))))}"
  IO.println s!"mergeM xs []: {Id.run (List.mergeM sx [] (fun x y => pure (decide (x ≤ y))))}"
  -- TimeM.merge / TimeM.mergeSort (LinearOrder ℕ, comparisons as ticks)
  let m := TimeM.merge sx sy
  IO.println s!"TimeM.merge ret: {m.ret} time: {m.time} (bound {sx.length + sy.length})"
  let ms := TimeM.mergeSort xs
  IO.println s!"TimeM.mergeSort ret: {ms.ret} time: {ms.time}"
  IO.println s!"rec bound: {TimeM.timeMergeSortRec xs.length} T: {TimeM.T xs.length}"
  -- bounds on many lengths
  let mut ok := true
  let mut lines : Array String := #[]
  for len in [0:40] do
    let l := genList (seed + len) len 1000
    let r := TimeM.mergeSort l
    let rec_ := TimeM.timeMergeSortRec len
    let t := TimeM.T len
    if !(r.time ≤ rec_ && rec_ ≤ t && r.ret == List.mergeSort l) then ok := false
    if len % 8 == 0 || len < 4 then lines := lines.push s!"{len}:{r.time}/{rec_}/{t}"
  IO.println s!"bounds hold for lengths 0..39: {ok}"
  IO.println s!"samples (len:time/rec/T): {lines}"
  IO.println s!"T 1000 = {TimeM.T 1000}, rec 1000 = {TimeM.timeMergeSortRec 1000}"
  IO.println s!"clog 2 of 1..9: {(List.range 9).map (fun i => Nat.clog 2 (i + 1))}"
  -- Int and String through LinearOrder
  let zs : List Int := xs.map (fun (x : Nat) => (x : Int) - 20)
  let mz := TimeM.mergeSort zs
  IO.println s!"Int TimeM.mergeSort: {mz.ret} time {mz.time}"
  let ws : List String := xs.map (fun x => s!"k{x % 11}-{x}")
  let mw := TimeM.mergeSort ws
  IO.println s!"String TimeM.mergeSort: {mw.ret} time {mw.time}"
  -- StateM counter vs TimeM
  let (s3, cnt) := (List.mergeSortM xs leState).run 0
  IO.println s!"StateM sorted==: {s3 == sx} count: {cnt} (TimeM {ms.time})"
  -- Except
  IO.println s!"Except ok: {showExc (List.mergeSortM xs (leExc 1000))}"
  IO.println s!"Except bad: {showExc (List.mergeSortM xs (leExc (xs.getD 2 0)))}"
  -- IO comparator (effects in order)
  let io ← List.mergeSortM ((xs.take 5).map (fun (x : Nat) => (x : Int) - 20)) leIO
  IO.println s!"IO sorted: {io}"
  -- stability: by key only
  let ps := (xs.zip (List.range xs.length)).map (fun (a, i) => (a % 4, i))
  let sp := Id.run (List.mergeSortM ps (fun a b => pure (decide (a.1 ≤ b.1))))
  IO.println s!"stable pairs: {sp}"
  -- TimeM functor/applicative instances
  let tm : TimeM ℕ Nat := pure (TimeM.mergeSort xs).ret.length
  IO.println s!"pure: {tm.ret} {tm.time}"
  let fm := (fun l => l.length) <$> TimeM.mergeSort xs
  IO.println s!"map: {fm.ret} {fm.time}"
  let sq := (TimeM.merge [1] [2]) *> (TimeM.mergeSort xs)
  IO.println s!"seqRight: {sq.ret.length} {sq.time}"
  let sl := (TimeM.merge [1] [2]) <* (TimeM.mergeSort xs)
  IO.println s!"seqLeft: {sl.ret} {sl.time}"
  let ap := (fun (a b : List Nat) => a ++ b) <$> TimeM.merge [5] [3] <*> TimeM.mergeSort [9, 8, 7]
  IO.println s!"seq: {ap.ret} {ap.time}"
  let tk : TimeM ℕ PUnit.{1} := TimeM.tick 5
  IO.println s!"tick: {tk.time}"
  -- big
  let big := genList (seed + 11) 5000 1000000
  let mb := TimeM.mergeSort big
  IO.println s!"big: len {mb.ret.length} sum {mb.ret.foldl (· + ·) 0} time {mb.time} rec {TimeM.timeMergeSortRec 5000} T {TimeM.T 5000} ok {mb.ret == List.mergeSort big}"
