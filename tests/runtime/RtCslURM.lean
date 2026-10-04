/-! Runtime test: CSLib's unlimited register machine (URM). `Instr` (derived
`DecidableEq` and `Repr`) with `readsFrom` (a `Finset`), `writesTo`,
`maxRegister`, `shiftJumps`, `shiftRegisters` and `capJump`; programs as
`List Instr` with `toStandardForm`; the decidable `Prop`s `IsJump`,
`JumpsBoundedBy`, `IsStraightLine` and `IsStandardForm` (instances by
`cases … infer_instance` and by `inferInstanceAs`); registers as functions
`Nat → Nat` updated by `Function.update` (a growing chain of closures),
and `State` with `Repr`. The program interprets an addition program, a
multiplication program and a program with out-of-range jumps (before and
after `toStandardForm`) with a step function that follows CSLib's `Step`
rules, and a larger multiplication. Arguments: two numbers.
A coverage test from CSLib (github.com/leanprover/cslib, commit 990e65a),
a library of computer science formalized in Lean: its computational code
only, proofs dropped, in one program that imports only Init. (A program
that imports CSLib imports Mathlib, which lean2rr does not support: plan
§10, "Not supported".) Mathlib code is from v4.34.0 (5ed2965), the version
CSLib 990e65a pins.
It draws on CSLib's Cslib/Computability/URM/Defs.lean, Basic.lean,
StraightLine.lean and StandardForm.lean, and follows the `Step` rules of
Cslib/Computability/URM/Execution.lean; it copies Mathlib's
`Function.update`. `NFinset` (a list without duplicates) is a new stand-in
for Mathlib's `Finset ℕ`. `step`, `run`, the programs and `main` are not
CSLib code: they are the round-9 driver, whose output on the real CSLib is
the same as this program's.
From the round-9 review, area cslib (rv9/cslib), program CslxURM.

Copyright notices of the copied code. It is used under the Apache License,
Version 2.0 (the file LICENSE of CSLib and of Mathlib;
http://www.apache.org/licenses/LICENSE-2.0) and changed here: the proofs
are removed and the Mathlib dependencies are replaced as described above.
* CSLib, Cslib/Computability/URM/Defs.lean:
    Copyright (c) 2026 Jesse Alama. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Jesse Alama
* CSLib, Cslib/Computability/URM/Basic.lean:
    Copyright (c) 2026 Jesse Alama. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Jesse Alama
* CSLib, Cslib/Computability/URM/StraightLine.lean:
    Copyright (c) 2026 Jesse Alama. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Jesse Alama
* CSLib, Cslib/Computability/URM/StandardForm.lean:
    Copyright (c) 2026 Jesse Alama. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Jesse Alama
* CSLib, Cslib/Computability/URM/Execution.lean (the `Step` rules):
    Copyright (c) 2026 Jesse Alama. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Jesse Alama
* Mathlib, Mathlib/Logic/Function/Basic.lean (`Function.update`):
    Copyright (c) 2016 Johannes Hölzl. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Johannes Hölzl, Mario Carneiro
-/

namespace Function
def update {α : Sort u} {β : α → Sort v} [DecidableEq α] (f : ∀ a, β a) (a' : α) (v : β a')
    (a : α) : β a :=
  if h : a = a' then Eq.ndrec v h.symm else f a
end Function

/-- `Finset ℕ` stand-in. -/
structure NFinset where
  elems : List Nat
instance : EmptyCollection NFinset := ⟨⟨[]⟩⟩
instance : Singleton Nat NFinset := ⟨fun a => ⟨[a]⟩⟩
instance : Insert Nat NFinset := ⟨fun a s => if s.elems.contains a then s else ⟨a :: s.elems⟩⟩
instance : Membership Nat NFinset := ⟨fun s a => a ∈ s.elems⟩
instance (a : Nat) (s : NFinset) : Decidable (a ∈ s) := inferInstanceAs (Decidable (a ∈ s.elems))
def NFinset.card (s : NFinset) : Nat := s.elems.length

namespace Cslib.URM

inductive Instr : Type where
  | Z : Nat → Instr
  | S : Nat → Instr
  | T : Nat → Nat → Instr
  | J : Nat → Nat → Nat → Instr
deriving DecidableEq, Repr

namespace Instr
def readsFrom : Instr → NFinset
  | Z _ => ∅
  | S n => {n}
  | T m _ => {m}
  | J m n _ => {m, n}
def writesTo : Instr → Option Nat
  | Z n => some n
  | S n => some n
  | T _ n => some n
  | J _ _ _ => none
def maxRegister : Instr → Nat
  | Z n => n
  | S n => n
  | T m n => max m n
  | J m n _ => max m n
def shiftJumps (offset : Nat) : Instr → Instr
  | Z n => Z n
  | S n => S n
  | T m n => T m n
  | J m n q => J m n (q + offset)
def shiftRegisters (offset : Nat) : Instr → Instr
  | Z n => Z (n + offset)
  | S n => S (n + offset)
  | T m n => T (m + offset) (n + offset)
  | J m n q => J (m + offset) (n + offset) q
end Instr

abbrev Regs := Nat → Nat
namespace Regs
def zero : Regs := fun _ => 0
def read (σ : Regs) (n : Nat) : Nat := σ n
def write (σ : Regs) (n : Nat) (v : Nat) : Regs := Function.update σ n v
def ofInputs (inputs : List Nat) : Regs := fun n => inputs.getD n 0
def output (σ : Regs) : Nat := σ 0
end Regs

abbrev Program := List Instr
namespace Program
def maxRegister (p : Program) : Nat :=
  p.foldl (fun acc instr => max acc instr.maxRegister) 0
def shiftJumps (p : Program) (offset : Nat) : Program :=
  p.map (Instr.shiftJumps offset)
def shiftRegisters (p : Program) (offset : Nat) : Program :=
  p.map (Instr.shiftRegisters offset)
end Program

structure State where
  pc : Nat
  regs : Regs

namespace State
def init (inputs : List Nat) : State := ⟨0, Regs.ofInputs inputs⟩
def isHalted (s : State) (p : Program) : Prop := p.length ≤ s.pc
instance (s : State) (p : Program) : Decidable (s.isHalted p) :=
  inferInstanceAs (Decidable (p.length ≤ s.pc))
instance : Inhabited State := ⟨init []⟩
instance : Repr State where
  reprPrec s _ := s!"State(pc={s.pc})"
end State

namespace Instr
def IsJump : Instr → Prop
  | J _ _ _ => True
  | _ => False
instance (instr : Instr) : Decidable instr.IsJump := by
  cases instr <;> simp only [IsJump] <;> infer_instance
def JumpsBoundedBy (len : Nat) : Instr → Prop
  | J _ _ q => q ≤ len
  | _ => True
instance (len : Nat) (instr : Instr) : Decidable (instr.JumpsBoundedBy len) := by
  cases instr <;> simp only [JumpsBoundedBy] <;> infer_instance
def capJump (len : Nat) : Instr → Instr
  | Z n => Z n
  | S n => S n
  | T m n => T m n
  | J m n q => J m n (min q len)
end Instr

def Program.IsStraightLine (p : Program) : Prop :=
  ∀ i ∈ p, ¬i.IsJump
instance (p : Program) : Decidable p.IsStraightLine :=
  inferInstanceAs (Decidable (∀ i ∈ p, ¬i.IsJump))

namespace Program
def IsStandardForm (p : Program) : Prop :=
  ∀ instr ∈ p, instr.JumpsBoundedBy p.length
instance (p : Program) : Decidable p.IsStandardForm :=
  inferInstanceAs (Decidable (∀ instr ∈ p, instr.JumpsBoundedBy p.length))
def toStandardForm (p : Program) : Program :=
  p.map (Instr.capJump p.length)
end Program

end Cslib.URM

open Cslib.URM Instr

/-- One step, following the rules of `Cslib.URM.Step`. -/
def step (p : Program) (s : State) : Option State :=
  match p[s.pc]? with
  | none => none
  | some (Z n) => some ⟨s.pc + 1, s.regs.write n 0⟩
  | some (S n) => some ⟨s.pc + 1, s.regs.write n (s.regs.read n + 1)⟩
  | some (T m n) => some ⟨s.pc + 1, s.regs.write n (s.regs.read m)⟩
  | some (J m n q) => if s.regs.read m = s.regs.read n then some ⟨q, s.regs⟩ else some ⟨s.pc + 1, s.regs⟩

def run (p : Program) (s : State) (fuel : Nat) (n : Nat := 0) : Nat × State :=
  match fuel with
  | 0 => (n, s)
  | fuel + 1 =>
    if decide (s.isHalted p) then (n, s) else
    match step p s with
    | none => (n, s)
    | some s' => run p s' fuel (n + 1)

/-- r0 := r0 + r1 (counter in r2). -/
def addP : Program := [J 1 2 4, S 0, S 2, J 0 0 0]
/-- r0 := r0 * r1: r3 accumulates, r2 counts outer, r4 counts inner. -/
def mulP : Program :=
  [ J 2 1 9,        -- 0: if r2 = r1 goto 9
    Z 4,            -- 1
    J 4 0 6,        -- 2: inner loop: if r4 = r0 goto 6
    S 3, S 4,       -- 3, 4
    J 0 0 2,        -- 5
    S 2,            -- 6
    J 0 0 0,        -- 7
    Z 0,            -- 8 (unreachable)
    T 3 0 ]         -- 9: r0 := r3
/-- A program with out-of-range jumps. -/
def wild : Program := [J 0 1 100, S 0, J 0 0 7, T 0 1]

def regsStr (s : State) (k : Nat) : String :=
  toString ((List.range k).map s.regs.read)

def main (args : List String) : IO Unit := do
  let a := (args.head? >>= String.toNat?).getD 7
  let b := ((args.drop 1).head? >>= String.toNat?).getD 5
  IO.println s!"addP: {repr addP}"
  let (n1, s1) := run addP (State.init [a, b]) 10000
  IO.println s!"add {a} {b}: steps {n1} out {s1.regs.output} regs {regsStr s1 4} halted {decide (s1.isHalted addP)} {repr s1}"
  let (n2, s2) := run mulP (State.init [a, b]) 100000
  IO.println s!"mul {a} {b}: steps {n2} out {s2.regs.output} regs {regsStr s2 5}"
  let (n3, s3) := run mulP (State.init [0, b]) 100000
  IO.println s!"mul 0 {b}: steps {n3} out {s3.regs.output}"
  IO.println s!"maxRegister add {addP.maxRegister} mul {mulP.maxRegister} wild {wild.maxRegister}"
  IO.println s!"standard? add {decide addP.IsStandardForm} mul {decide mulP.IsStandardForm} wild {decide wild.IsStandardForm}"
  let w := wild.toStandardForm
  IO.println s!"toStandardForm wild: {repr w} standard {decide w.IsStandardForm}"
  let (n4, s4) := run w (State.init [a, a + 1]) 100
  IO.println s!"run std wild: steps {n4} pc {s4.pc} regs {regsStr s4 2}"
  IO.println s!"straight? add {decide addP.IsStraightLine} [S 0, T 0 1] {decide (Program.IsStraightLine [S 0, T 0 1])}"
  IO.println s!"isJump: {[Z 1, S 1, T 1 2, J 1 2 3].map fun i => decide i.IsJump}"
  IO.println s!"shiftJumps 10: {repr (addP.shiftJumps 10)}"
  IO.println s!"shiftRegisters 3: {repr (addP.shiftRegisters 3)}"
  -- composing: shifted add after itself
  let twice : Program := addP ++ (addP.shiftJumps addP.length)
  let (n5, s5) := run twice (State.init [a, b]) 10000
  IO.println s!"add twice: steps {n5} out {s5.regs.output} regs {regsStr s5 3}"
  -- readsFrom (Finset): card and membership
  for i in [Z 3, S 4, T 1 2, J 2 2 0, J 1 a 0] do
    let r := i.readsFrom
    IO.println s!"{repr i}: reads card {r.card} has0 {decide (0 ∈ r)} has1 {decide (1 ∈ r)} has2 {decide (2 ∈ r)} writes {i.writesTo} max {i.maxRegister} cap3 {repr (i.capJump 3)}"
  IO.println s!"instr eq: {decide (J 1 2 3 = J 1 2 3)} {decide (J 1 2 3 = J 1 2 4)} {decide (Z 0 = S 0)}"
  let big := a * 37 + 11
  let (n6, s6) := run mulP (State.init [big, b + 3]) 1000000
  IO.println s!"mul {big} {b + 3}: steps {n6} out {s6.regs.output}"
