/-! Runtime test: CSLib's CCS terms and Milner's vending machine. `Act`,
`Process` and `Context` are inductives with two universe parameters and
derived `DecidableEq`, with `Act.isCo` and `Context.fill`; `vm`,
`vendingDefs` (coin.(tea.VM + coffee.VM)) and `vendingDefsND`
(coin.tea.VM + coin.coffee.VM) are CSLib's two vending machines, a
constant and its definitions. The program prints the processes, compares
them by `decide`, and explores both machines with a one-step transition
function that follows CSLib's `Tr` rules (a `partial def`): the reachable
states, the traces of a given length, the offers after a coin, and a
system of a machine in parallel with a customer under restriction; it also
fills contexts. Argument: the exploration depth.
A coverage test from CSLib (github.com/leanprover/cslib, commit 990e65a),
a library of computer science formalized in Lean: its computational code
only, proofs dropped, in one program that imports only Init. (A program
that imports CSLib imports Mathlib, which lean2rr does not support: plan
§10, "Not supported".) Mathlib code is from v4.34.0 (5ed2965), the version
CSLib 990e65a pins.
It draws on CSLib's Cslib/Languages/CCS/Basic.lean and
Cslib/Algorithms/CCS/VendingMachine.lean (its `(CCS| …)` quotations are
written out as constructor terms), and follows the `Tr` rules of
Cslib/Languages/CCS/Semantics.lean. `showAct`, `showProc`, `steps`,
`explore`, `traces`, `customer` and `main` are not CSLib code: they are
the round-9 driver, whose output on the real CSLib is the same as this
program's.
From the round-9 review, area cslib (rv9/cslib), program CslxVending.

Copyright notices of the copied code. It is used under the Apache License,
Version 2.0 (the file LICENSE of CSLib and of Mathlib;
http://www.apache.org/licenses/LICENSE-2.0) and changed here: the proofs
are removed and the Mathlib dependencies are replaced as described above.
* CSLib, Cslib/Languages/CCS/Basic.lean:
    Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Fabrizio Montesi
* CSLib, Cslib/Languages/CCS/Semantics.lean (the `Tr` rules):
    Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Fabrizio Montesi
* CSLib, Cslib/Algorithms/CCS/VendingMachine.lean:
    Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Fabrizio Montesi
-/

namespace Cslib.CCS
universe u v

inductive Act (Name : Type u) : Type u where
  | name (a : Name)
  | coname (a : Name)
  | τ
deriving DecidableEq

inductive Process (Name : Type u) (Constant : Type v) : Type (max u v) where
  | nil
  | pre (μ : Act Name) (p : Process Name Constant)
  | par (p q : Process Name Constant)
  | choice (p q : Process Name Constant)
  | res (a : Name) (p : Process Name Constant)
  | const (c : Constant)
deriving DecidableEq

namespace Act
def isCo [DecidableEq Name] (μ μ' : Act Name) : Bool :=
  match μ, μ' with
  | name a, coname b | coname a, name b => a = b
  | _, _ => false
end Act

inductive Context (Name : Type u) (Constant : Type v) : Type (max u v) where
  | hole
  | pre (μ : Act Name) (c : Context Name Constant)
  | parL (c : Context Name Constant) (q : Process Name Constant)
  | parR (p : Process Name Constant) (c : Context Name Constant)
  | choiceL (c : Context Name Constant) (q : Process Name Constant)
  | choiceR (p : Process Name Constant) (c : Context Name Constant)
  | res (a : Name) (c : Context Name Constant)
deriving DecidableEq

def Context.fill (c : Context Name Constant) (p : Process Name Constant) : Process Name Constant :=
  match c with
  | hole => p
  | pre μ c => Process.pre μ (c.fill p)
  | parL c r => Process.par (c.fill p) r
  | parR r c => Process.par r (c.fill p)
  | choiceL c r => Process.choice (c.fill p) r
  | choiceR r c => Process.choice r (c.fill p)
  | res a c => Process.res a (c.fill p)

end Cslib.CCS

namespace Cslib.Algorithms.CCS.VendingMachine
open Cslib.CCS Process Act

abbrev Coin := name "coin"
abbrev Tea := name "tea"
abbrev Coffee := name "coffee"

inductive Constant
  | vm

def vm : Process String Constant := Process.const .vm

def vendingDefs : Constant → Option (Process String Constant)
  | .vm => some <| Process.pre Coin (Process.choice (Process.pre Tea (Process.const .vm))
      (Process.pre Coffee (Process.const .vm)))

def vendingDefsND : Constant → Option (Process String Constant)
  | .vm => some <| Process.choice (Process.pre Coin (Process.pre Tea (Process.const .vm)))
      (Process.pre Coin (Process.pre Coffee (Process.const .vm)))

end Cslib.Algorithms.CCS.VendingMachine

open Cslib.CCS Cslib.Algorithms.CCS.VendingMachine

deriving instance DecidableEq for Constant

def showAct : Act String → String
  | .name a => a
  | .coname a => s!"'{a}"
  | .τ => "τ"

def showProc : Process String Constant → String
  | .nil => "0"
  | .pre μ p => s!"{showAct μ}.{showProc p}"
  | .par p q => s!"({showProc p} | {showProc q})"
  | .choice p q => s!"({showProc p} + {showProc q})"
  | .res a p => s!"(ν{a} {showProc p})"
  | .const .vm => "VM"

/-- One-step transitions following `Cslib.CCS.Tr` (constants unfolded once per step). -/
partial def steps (defs : Constant → Option (Process String Constant)) :
    Process String Constant → List (Act String × Process String Constant)
  | .nil => []
  | .pre μ p => [(μ, p)]
  | .par p q =>
    let sp := steps defs p
    let sq := steps defs q
    sp.map (fun (μ, p') => (μ, .par p' q)) ++ sq.map (fun (μ, q') => (μ, .par p q')) ++
      (sp.flatMap fun (μ, p') => sq.filterMap fun (nu, q') =>
        if Act.isCo μ nu then some (.τ, .par p' q') else none)
  | .choice p q => steps defs p ++ steps defs q
  | .res a p => (steps defs p).filter (fun (μ, _) => μ != .name a && μ != .coname a)
      |>.map (fun (μ, p') => (μ, .res a p'))
  | .const k => match defs k with
    | some p => steps defs p
    | none => []

/-- Breadth-first reachable states (up to `fuel` rounds). -/
def explore (defs : Constant → Option (Process String Constant)) (start : Process String Constant)
    (fuel : Nat) : List (Process String Constant) := Id.run do
  let mut seen : List (Process String Constant) := [start]
  let mut frontier := [start]
  for _ in [0:fuel] do
    let mut next := []
    for p in frontier do
      for (_, q) in steps defs p do
        if !seen.contains q then
          seen := seen ++ [q]
          next := next ++ [q]
    frontier := next
  return seen

/-- The traces of length `n` (as lists of action names). -/
def traces (defs : Constant → Option (Process String Constant)) : Nat → Process String Constant →
    List (List String)
  | 0, _ => [[]]
  | n + 1, p =>
    let ts := (steps defs p).flatMap fun (μ, q) => (traces defs n q).map (showAct μ :: ·)
    if ts.isEmpty then [[]] else ts

def customer (drink : String) : Process String Constant :=
  .pre (.coname "coin") (.pre (.coname drink) .nil)

def main (args : List String) : IO Unit := do
  let depth := (args.head? >>= String.toNat?).getD 3
  IO.println s!"vm = {showProc vm}"
  IO.println s!"D: vm := {(vendingDefs .vm).map showProc}"
  IO.println s!"ND: vm := {(vendingDefsND .vm).map showProc}"
  IO.println s!"Coin = {showAct Coin}, Tea = {showAct Tea}, Coffee = {showAct Coffee}"
  IO.println s!"isCo coin 'coin: {Act.isCo Coin (.coname "coin")}, coin coin: {Act.isCo Coin Coin}, τ τ: {Act.isCo (Act.τ : Act String) .τ}"
  IO.println s!"decEq Tea Coffee: {decide (Tea = Coffee)}, Tea Tea: {decide (Tea = Tea)}"
  IO.println s!"decEq defs: {decide (vendingDefs .vm = vendingDefsND .vm)}, self {decide (vendingDefs .vm = vendingDefs .vm)}"
  for (name, defs) in [("D", vendingDefs), ("ND", vendingDefsND)] do
    IO.println s!"{name} steps(vm): {(steps defs vm).map fun (μ, p) => s!"{showAct μ}->{showProc p}"}"
    let r := explore defs vm depth
    IO.println s!"{name} reachable ({r.length}): {r.map showProc}"
    IO.println s!"{name} traces {depth}: {traces defs depth vm}"
    -- after `coin`, can the machine still offer both drinks?
    let afterCoin := (steps defs vm).filter (·.1 == Coin) |>.map (·.2)
    let offers := afterCoin.map fun p => (steps defs p).map (showAct ·.1)
    IO.println s!"{name} offers after coin: {offers}"
    -- a customer in parallel, restricted on coin/drink
    let sys : Process String Constant :=
      .res "coin" (.res "tea" (.par vm (customer "tea")))
    let r2 := explore defs sys (depth + 1)
    IO.println s!"{name} system reachable ({r2.length}): {r2.map showProc}"
  -- contexts
  let c : Context String Constant := .res "coin" (.parL (.choiceR .nil .hole) (customer "tea"))
  IO.println s!"fill: {showProc (c.fill vm)}"
  IO.println s!"fill nested: {showProc ((Context.pre Coin (.choiceL .hole (.const .vm))).fill (c.fill .nil))}"
  IO.println s!"ctx decEq: {decide (c = c)}, {decide (c = .hole)}"
