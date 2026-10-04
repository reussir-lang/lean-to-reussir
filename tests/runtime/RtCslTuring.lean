/-! Runtime test: CSLib's Turing machine interpreters. Single tape:
`SingleTapeTM` is a structure with a type field (`State`) and an instance
field (`Fintype State`), and its configurations have the dependent type
`tm.Cfg`; the tape is a `BiTape` of two `StackTape`s (structures with a
proof field); `step`, `initCfg`, `haltCfg`, `Cfg.spaceUsed`, `idComputer`
and `compComputer` (the composed machine's states are a sum type). The
program runs a binary increment machine (up to 2^64 + k, a big number),
compositions of it, the identity machine and an eraser, and moves a tape
off both ends. Multi-tape: `MultiTapeTM`, `Action.apply`, `Cfg` with an
input position in `Fin (input.length + 2)` and work tapes as functions
`Fin k → Int → Option Symbol` updated by `Function.update`, `runFrom`
(`Nat.iterate`), `haltsAtStep`, `visitedByTapeHead` and `spaceUsed`, and
`SignType` head moves cast to `Int`; the program runs a one-tape reverse
machine and a two-tape majority machine. Argument: a number.
A coverage test from CSLib (github.com/leanprover/cslib, commit 990e65a),
a library of computer science formalized in Lean: its computational code
only, proofs dropped, in one program that imports only Init. (A program
that imports CSLib imports Mathlib, which lean2rr does not support: plan
§10, "Not supported".) Mathlib code is from v4.34.0 (5ed2965), the version
CSLib 990e65a pins.
It draws on CSLib's Cslib/Foundations/Data/StackTape.lean,
Cslib/Foundations/Data/BiTape.lean,
Cslib/Computability/Machines/Turing/SingleTape/Deterministic.lean,
Cslib/Computability/Machines/Turing/MultiTape/Configuration.lean and
Cslib/Computability/Machines/Turing/MultiTape/Deterministic.lean, and
copies Mathlib's `SignType` (with its cast), `Turing.Dir`, `Nat.iterate`
and `Function.update`. `Fintype` (a class that holds the element list) and
the `Finset ℤ` of `visitedByTapeHead` (a list without duplicates) are new
stand-ins for Mathlib's. The machines `incTM`, `eraseFalseTM`, `revTM`
and `majTM`, the helpers and `main` are not CSLib code: they are the
round-9 driver, whose output on the real CSLib is the same as this
program's.
From the round-9 review, area cslib (rv9/cslib), program CslxTuring.

Copyright notices of the copied code. It is used under the Apache License,
Version 2.0 (the file LICENSE of CSLib and of Mathlib;
http://www.apache.org/licenses/LICENSE-2.0) and changed here: the proofs
are removed and the Mathlib dependencies are replaced as described above.
* CSLib, Cslib/Foundations/Data/StackTape.lean:
    Copyright (c) 2026 Bolton Bailey. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Bolton Bailey
* CSLib, Cslib/Foundations/Data/BiTape.lean:
    Copyright (c) 2026 Bolton Bailey. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Bolton Bailey
* CSLib, Cslib/Computability/Machines/Turing/SingleTape/Deterministic.lean:
    Copyright (c) 2026 Bolton Bailey. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Bolton Bailey, Pim Spelier, Daan van Gent
* CSLib, Cslib/Computability/Machines/Turing/MultiTape/Configuration.lean:
    Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Christian Reitwiessner, Aviv Bar Natan
* CSLib, Cslib/Computability/Machines/Turing/MultiTape/Deterministic.lean:
    Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Christian Reitwiessner, Samuel Schlesinger
* Mathlib, Mathlib/Basic/Sign/Defs.lean (`SignType`, its instances, `cast`):
    Copyright (c) 2022 Eric Rodriguez. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Eric Rodriguez
* Mathlib, Mathlib/Computability/TuringMachine/Tape.lean (`Turing.Dir`):
    Copyright (c) 2018 Mario Carneiro. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Mario Carneiro
* Mathlib, Mathlib/Logic/Function/Iterate.lean (`Nat.iterate`):
    Copyright (c) 2020 Yury Kudryashov. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Yury Kudryashov
* Mathlib, Mathlib/Logic/Function/Basic.lean (`Function.update`):
    Copyright (c) 2016 Johannes Hölzl. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Johannes Hölzl, Mario Carneiro
-/

/-! ### Mathlib stand-ins -/
inductive SignType
  | zero
  | neg
  | pos
  deriving DecidableEq, Inhabited

namespace SignType
instance : Zero SignType := ⟨zero⟩
instance : One SignType := ⟨pos⟩
instance : Neg SignType :=
  ⟨fun s =>
    match s with
    | neg => pos
    | zero => zero
    | pos => neg⟩
def cast {α : Type u} [Zero α] [One α] [Neg α] : SignType → α
  | zero => 0
  | pos => 1
  | neg => -1
instance {α : Type u} [Zero α] [One α] [Neg α] (s : SignType) : CoeDep SignType s α := ⟨cast s⟩
end SignType

namespace Turing
inductive Dir
  | left
  | right
  deriving DecidableEq, Inhabited
end Turing

/-- Mathlib `Mathlib/Logic/Function/Iterate.lean`, copied. -/
def Nat.iterate {α : Sort u} (op : α → α) : Nat → α → α
  | 0, a => a
  | Nat.succ k, a => Nat.iterate op k (op a)

namespace Function
def update {α : Sort u} {β : α → Sort v} [DecidableEq α] (f : ∀ a, β a) (a' : α) (v : β a')
    (a : α) : β a :=
  if h : a = a' then Eq.ndrec v h.symm else f a
end Function

class Fintype (α : Type u) where
  elems : List α
instance : Fintype Bool := ⟨[false, true]⟩
instance : Fintype (Fin n) := ⟨List.finRange n⟩
instance : Fintype PUnit := ⟨[PUnit.unit]⟩
instance [Fintype α] [Fintype β] : Fintype (α ⊕ β) :=
  ⟨(Fintype.elems (α := α)).map .inl ++ (Fintype.elems (α := β)).map .inr⟩

/-! ### CSLib `Cslib/Foundations/Data/StackTape.lean`, `BiTape.lean` (code) -/
namespace Cslib.Turing

structure StackTape (Symbol : Type u) where
  toList : List (Option Symbol)
  toList_getLast?_ne_some_none : toList.getLast? ≠ some none

namespace StackTape
variable {Symbol : Type u}
def nil : StackTape Symbol := ⟨[], by simp⟩
instance : Inhabited (StackTape Symbol) where
  default := nil
instance : EmptyCollection (StackTape Symbol) :=
  ⟨nil⟩
def cons (x : Option Symbol) (xs : StackTape Symbol) : StackTape Symbol :=
  match x, xs with
  | none, ⟨[], _⟩ => ⟨[], by simp⟩
  | none, ⟨hd :: tl, hl⟩ => ⟨none :: hd :: tl, by grind⟩
  | some a, ⟨l, hl⟩ => ⟨some a :: l, by grind⟩
def tail (l : StackTape Symbol) : StackTape Symbol :=
  match hl : l.toList with
  | [] => nil
  | hd :: t => ⟨t, by have := l.toList_getLast?_ne_some_none; grind⟩
def head (l : StackTape Symbol) : Option Symbol :=
  match l.toList with
  | [] => none
  | h :: _ => h
def mapSome (l : List Symbol) : StackTape Symbol := ⟨l.map some, by
  rw [List.getLast?_map]; cases l.getLast? <;> simp⟩
def length (l : StackTape Symbol) : Nat := l.toList.length
end StackTape

structure BiTape (Symbol : Type u) where
  head : Option Symbol
  left : StackTape Symbol
  right : StackTape Symbol

namespace BiTape
variable {Symbol : Type u}
def nil : BiTape Symbol := ⟨none, ∅, ∅⟩
instance : Inhabited (BiTape Symbol) where
  default := nil
instance : EmptyCollection (BiTape Symbol) :=
  ⟨nil⟩
def mk₁ (l : List Symbol) : BiTape Symbol :=
  match l with
  | [] => ∅
  | h :: t => { head := some h, left := ∅, right := StackTape.mapSome t }
def moveLeft (t : BiTape Symbol) : BiTape Symbol :=
  ⟨t.left.head, t.left.tail, StackTape.cons t.head t.right⟩
def moveRight (t : BiTape Symbol) : BiTape Symbol :=
  ⟨t.right.head, StackTape.cons t.head t.left, t.right.tail⟩
open _root_.Turing
def move (t : BiTape Symbol) : Dir → BiTape Symbol
  | .left => t.moveLeft
  | .right => t.moveRight
def optionMove : BiTape Symbol → Option Turing.Dir → BiTape Symbol
  | t, none => t
  | t, some d => t.move d
def write (t : BiTape Symbol) (a : Option Symbol) : BiTape Symbol := { t with head := a }
def spaceUsed (t : BiTape Symbol) : Nat := 1 + t.left.length + t.right.length
end BiTape

/-! ### CSLib `.../Turing/SingleTape/Deterministic.lean` (code) -/
open BiTape StackTape
open _root_.Turing
variable {Symbol : Type}

namespace SingleTapeTM
structure Stmt (Symbol : Type) where
  symbol : Option Symbol
  movement : Option Dir
deriving Inhabited
end SingleTapeTM

structure SingleTapeTM Symbol [Inhabited Symbol] [Fintype Symbol] where
  (State : Type)
  [stateFintype : Fintype State]
  (q₀ : State)
  (tr : State → Option Symbol → SingleTapeTM.Stmt Symbol × Option State)

namespace SingleTapeTM
section Cfg
variable [Inhabited Symbol] [Fintype Symbol] (tm : SingleTapeTM Symbol)
instance : Inhabited tm.State := ⟨tm.q₀⟩
instance : Fintype tm.State := tm.stateFintype
instance inhabitedStmt : Inhabited (Stmt Symbol) := inferInstance
structure Cfg : Type where
  state : Option tm.State
  BiTape : BiTape Symbol
deriving Inhabited
def step : tm.Cfg → Option tm.Cfg
  | ⟨none, _⟩ =>
    none
  | ⟨some q', t⟩ =>
    match tm.tr q' t.head with
    | ⟨⟨wr, dir⟩, q''⟩ => some ⟨q'', (t.write wr).optionMove dir⟩
def initCfg (tm : SingleTapeTM Symbol) (s : List Symbol) : tm.Cfg := ⟨some tm.q₀, BiTape.mk₁ s⟩
def haltCfg (tm : SingleTapeTM Symbol) (s : List Symbol) : tm.Cfg := ⟨none, BiTape.mk₁ s⟩
def Cfg.spaceUsed (tm : SingleTapeTM Symbol) (cfg : tm.Cfg) : Nat := cfg.BiTape.spaceUsed
end Cfg
variable [Inhabited Symbol] [Fintype Symbol]
def idComputer : SingleTapeTM Symbol where
  State := PUnit
  q₀ := PUnit.unit
  tr _ b := ⟨⟨b, none⟩, none⟩
def compComputer (tm1 tm2 : SingleTapeTM Symbol) : SingleTapeTM Symbol where
  State := tm1.State ⊕ tm2.State
  q₀ := .inl tm1.q₀
  tr q h :=
    match q with
    | .inl ql => match tm1.tr ql h with
      | (stmt, state) =>
        (stmt,
          match state with
          | none => some (.inr tm2.q₀)
          | _ => Option.map .inl state)
    | .inr qr =>
      match tm2.tr qr h with
      | (stmt, state) =>
        (stmt,
          match state with
          | none => none
          | _ => Option.map .inr state)
end SingleTapeTM
end Cslib.Turing

/-! ### CSLib `.../Turing/MultiTape/Configuration.lean`, `Deterministic.lean` (code) -/
namespace Turing
variable {k : Nat} {State Symbol : Type u} {input : List Symbol}

structure Action (k : Nat) (Symbol State : Type u) where
  inputTape : SignType
  workTapes : Fin k → (Option (Option Symbol)) × SignType
  output : Option Symbol
  state : Option State

structure Cfg (k : Nat) (Symbol State : Type u) (input : List Symbol) where
  state : Option State
  inputPos : Fin (input.length + 2)
  workTapes : Fin k → Int → Option Symbol
  workTapePos : Fin k → Int
  output : List Symbol

instance : Inhabited (Cfg k Symbol State input) := ⟨⟨none, 0, fun _ _ => none, fun _ => 0, []⟩⟩

def moveInputPos {n : Nat} (pos : Fin (n + 2)) (m : SignType) : Fin (n + 2) :=
  let p := ((pos.val : Int) + (m.cast : Int)).toNat
  if h : p < n + 2 then ⟨p, h⟩ else ⟨n + 1, by omega⟩

def Cfg.inputSymbol (cfg : Cfg k Symbol State input) : Option Symbol :=
  if h₁ : cfg.inputPos = 0 then none
  else if h₂ : cfg.inputPos = input.length + 1 then none
  else input[cfg.inputPos.val - 1]'(by grind)

def Cfg.workTapeSymbols (cfg : Cfg k Symbol State input) (i : Fin k) : Option Symbol :=
  cfg.workTapes i (cfg.workTapePos i)

def Cfg.init (q₀ : State) (input : List Symbol) : Cfg k Symbol State input :=
  ⟨some q₀, 1, fun _ _ => none, fun _ => 0, []⟩

def Action.apply (action : Action k Symbol State) (cfg : Cfg k Symbol State input) :
    Cfg k Symbol State input where
  state := action.state
  inputPos := moveInputPos cfg.inputPos action.inputTape
  workTapes i := match (action.workTapes i).1 with
    | none => cfg.workTapes i
    | some s => Function.update (cfg.workTapes i) (cfg.workTapePos i) s
  workTapePos i := cfg.workTapePos i + (action.workTapes i).2
  output := cfg.output ++ action.output.toList
end Turing

open Turing
variable {k : Nat} {State Symbol : Type u}

structure MultiTapeTM (k : Nat) (Symbol State : Type u) where
  q₀ : State
  tr (q : State) (input : Option Symbol) (work : Fin k → Option Symbol) :
    Action k Symbol State

namespace MultiTapeTM
variable (tm : MultiTapeTM k Symbol State) {input : List Symbol}
def step (cfg : Cfg k Symbol State input) : Cfg k Symbol State input :=
  match cfg.state with
  | none => cfg
  | some q => (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg
def outputSymbol (cfg : Cfg k Symbol State input) : Option Symbol :=
  match cfg.state with
  | none => none
  | some q => (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).output
def initCfg (input : List Symbol) : Cfg k Symbol State input := Cfg.init tm.q₀ input
def runFrom (cfg : Cfg k Symbol State input) (t : Nat) : Cfg k Symbol State input := Nat.iterate tm.step t cfg
/-- `Finset ℤ` stand-in: `(Finset.range (t + 1)).image f` as a deduplicated list. -/
def visitedByTapeHead (cfg : Cfg k Symbol State input) (t : Nat) (i : Fin k) : List Int :=
  ((List.range (t + 1)).map fun t' => (tm.runFrom cfg t').workTapePos i).eraseDups
def spaceUsedByTape (cfg : Cfg k Symbol State input) (t : Nat) (i : Fin k) : Nat :=
  (tm.visitedByTapeHead cfg t i).length
def spaceUsed (cfg : Cfg k Symbol State input) (t : Nat) : Nat :=
  (List.finRange k).foldr (fun i acc => tm.spaceUsedByTape cfg t i + acc) 0
def haltsAtStep (input : List Symbol) (t : Nat) : Bool :=
  (tm.runFrom (tm.initCfg input) t).state.isNone &&
  !(tm.runFrom (tm.initCfg input) (t - 1)).state.isNone
end MultiTapeTM

open Cslib.Turing Turing

/-! ## Single tape -/

/-- Binary increment, least significant bit first: flip trailing 1s, then write a 1.
Then walk back to the left end (state 2) so the head halts at the start. -/
def incTM : SingleTapeTM Bool where
  State := Fin 3
  q₀ := 0
  tr q s := match q.val, s with
    | 0, some true => (⟨some false, some .right⟩, some 0)
    | 0, some false => (⟨some true, some .left⟩, some 1)
    | 0, none => (⟨some true, some .left⟩, some 1)
    | _, none => (⟨none, some .right⟩, none)
    | _, some b => (⟨some b, some .left⟩, some 1)

/-- Erase every `false` (unary-ish filter): walks right writing blanks over `false`. -/
def eraseFalseTM : SingleTapeTM Bool where
  State := Bool
  q₀ := true
  tr q s := match q, s with
    | true, some false => (⟨none, some .right⟩, some true)
    | true, some true => (⟨some true, some .right⟩, some true)
    | true, none => (⟨none, none⟩, none)
    | false, _ => (⟨none, none⟩, none)

def showTape (t : BiTape Bool) : String :=
  let bit : Option Bool → String := fun | some true => "1" | some false => "0" | none => "_"
  s!"{String.join (t.left.toList.reverse.map bit)}[{bit t.head}]{String.join (t.right.toList.map bit)}"

def runTM1 (tm : SingleTapeTM Bool) (c : tm.Cfg) (fuel : Nat) (n : Nat := 0) : Nat × tm.Cfg :=
  match fuel with
  | 0 => (n, c)
  | fuel + 1 => match tm.step c with
    | none => (n, c)
    | some c' => runTM1 tm c' fuel (n + 1)

def bitsOf (k : Nat) : List Bool :=
  if k = 0 then [] else (k % 2 == 1) :: bitsOf (k / 2)

def valOf (t : BiTape Bool) : Nat :=
  let cells := t.left.toList.reverse ++ [t.head] ++ t.right.toList
  cells.foldr (fun c acc => acc * 2 + (if c == some true then 1 else 0)) 0

/-! ## Multi-tape -/

inductive St | copy | back | out
  deriving DecidableEq, Repr

/-- One work tape: copy the input onto it, then emit it backwards (reverse). -/
def revTM : MultiTapeTM 1 Bool St where
  q₀ := .copy
  tr q i w :=
    match q, i with
    | .copy, some b => ⟨.pos, fun _ => (some (some b), .pos), none, some .copy⟩
    | .copy, none => ⟨0, fun _ => (none, .neg), none, some .out⟩
    | .back, _ => ⟨0, fun _ => (none, .neg), none, some .out⟩
    | .out, _ => match w 0 with
      | some b => ⟨0, fun _ => (none, .neg), some b, some .out⟩
      | none => ⟨0, fun _ => (none, 0), none, none⟩

/-- Two work tapes: count the `true`s in unary on tape 0 and the `false`s on tape 1, then
output `true` iff there are more `true`s (compares by walking both tapes back). -/
inductive Cmp | scan | cmp
  deriving DecidableEq

def majTM : MultiTapeTM 2 Bool Cmp where
  q₀ := .scan
  tr q i w :=
    match q, i with
    | .scan, some true => ⟨.pos, fun j => if j = 0 then (some (some true), .pos) else (none, 0),
        none, some .scan⟩
    | .scan, some false => ⟨.pos, fun j => if j = 1 then (some (some true), .pos) else (none, 0),
        none, some .scan⟩
    | .scan, none => ⟨0, fun _ => (none, .neg), none, some .cmp⟩
    | .cmp, _ => match w 0, w 1 with
      | some _, some _ => ⟨0, fun _ => (none, .neg), none, some .cmp⟩
      | some _, none => ⟨0, fun _ => (none, 0), some true, none⟩
      | _, _ => ⟨0, fun _ => (none, 0), some false, none⟩

def bitsStr (l : List Bool) : String := String.join (l.map fun b => if b then "1" else "0")

def haltTime {k : Nat} {St : Type} (tm : MultiTapeTM k Bool St) (input : List Bool) (bound : Nat) :
    Option Nat :=
  (List.range bound).find? (tm.haltsAtStep input)

def main (args : List String) : IO Unit := do
  let k := (args.head? >>= String.toNat?).getD 11
  -- single tape: increment
  for v in [k, 0, 1, 7, 2 ^ 20 - 1, 2 ^ 64 + k] do
    let (n, c) := runTM1 incTM (incTM.initCfg (bitsOf v)) 1000
    IO.println s!"inc {v}: steps {n} halted {c.state.isNone} tape {showTape c.BiTape} value {valOf c.BiTape} space {c.spaceUsed}"
  -- composition: inc ∘ inc, id
  let twice := SingleTapeTM.compComputer incTM incTM
  let (n2, c2) := runTM1 twice (twice.initCfg (bitsOf k)) 1000
  IO.println s!"inc∘inc {k}: steps {n2} value {valOf c2.BiTape} tape {showTape c2.BiTape}"
  let thrice := SingleTapeTM.compComputer twice incTM
  let (n3, c3) := runTM1 thrice (thrice.initCfg (bitsOf (k * 5))) 1000
  IO.println s!"inc∘inc∘inc {k * 5}: steps {n3} value {valOf c3.BiTape}"
  let (ni, ci) := runTM1 SingleTapeTM.idComputer (SingleTapeTM.idComputer.initCfg (bitsOf k)) 10
  IO.println s!"id {k}: steps {ni} tape {showTape ci.BiTape}"
  let (ne, ce) := runTM1 eraseFalseTM (eraseFalseTM.initCfg (bitsOf (k * 37))) 100
  IO.println s!"eraseFalse {bitsStr (bitsOf (k * 37))}: steps {ne} tape {showTape ce.BiTape}"
  IO.println s!"halt cfg space: {(incTM.haltCfg (bitsOf k)).spaceUsed}, nil tape {showTape (BiTape.nil : BiTape Bool)}"
  -- BiTape moves off both ends
  let t := (BiTape.mk₁ [true, false]).moveLeft.moveLeft.write (some true) |>.moveRight.moveRight.moveRight.moveRight
  IO.println s!"bitape moves: {showTape t} space {t.spaceUsed}"
  -- multi tape: reverse
  let inputs : List (List Bool) := [bitsOf k, [], [true], bitsOf (k * 1000 + 3)]
  for inp in inputs do
    let bound := 2 * inp.length + 4
    let c := revTM.runFrom (revTM.initCfg inp) bound
    IO.println s!"rev {bitsStr inp}: out {bitsStr c.output} halted {c.state.isNone} haltAt {haltTime revTM inp bound} space {revTM.spaceUsed (revTM.initCfg inp) bound} pos {c.workTapePos 0} inPos {c.inputPos.val}"
  -- two tapes: majority
  for inp in [bitsOf k, bitsOf (k * 3 + 1), [true, true, false], [false, false, true], []] do
    let bound := 2 * inp.length + 4
    let c := majTM.runFrom (majTM.initCfg inp) bound
    IO.println s!"maj {bitsStr inp}: out {bitsStr c.output} haltAt {haltTime majTM inp bound} space {majTM.spaceUsed (majTM.initCfg inp) bound} visited0 {(majTM.visitedByTapeHead (majTM.initCfg inp) bound 0).length}"
  IO.println s!"moveInputPos: {(moveInputPos (0 : Fin 5) .neg).val} {(moveInputPos (4 : Fin 5) .pos).val} {(moveInputPos (2 : Fin 5) .pos).val}"
