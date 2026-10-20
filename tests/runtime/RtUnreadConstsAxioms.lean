/-! Runtime test of the optimization `unread-consts` (hunt r7 B and its
review): a constant whose declaration rests on a claim Lean did not check
is not left out (RtUnreadConstsAxioms.l2r-debug checks the decisions): an
axiom other than `propext`, `Quot.sound` and `Classical.choice` (`sorry`,
a user axiom, `native_decide`), also in the compiled code of a `partial`
definition (`f._unsafe_rec`) or in a `@[csimp]` theorem (also a `local`
one), and an `@[implemented_by]` of the program. A false claim can make the evaluation
of a constant panic (`unreach`, test `RtUnreadConstsSorry`) or run for
ever: `for i in r` over a `Std.Legacy.Range` whose step is 0 at run time
loops natively (`Std.Legacy.Range.forIn'` is well-founded recursion on
`step_pos`), and the pass trusted Lean's library recursion to end. Here
every loop ends (the ranges are empty), so the run is the same; only the
decisions show. -/

-- `sorry` in a proof field: `r0` and the constant that loops over it stay.
def r0 : Std.Legacy.Range := { stop := 0, step := 0, step_pos := sorry }

def spin : Nat := Id.run do
  let mut s := 0
  for i in r0 do
    s := s + i
  return s

-- An axiom of the program.
axiom stepPos : 0 < 0

def r1 : Std.Legacy.Range := { stop := 0, step := 0, step_pos := stepPos }

-- `native_decide`: Lean 4.34 adds an axiom for each use
-- (`byNative._native.native_decide.ax_1_1`), not standard.
theorem byNative : 3 < 4 := by native_decide

def viaNative : Fin 4 := ⟨3, byNative⟩

-- `sorry` only in the code that runs of a `partial` definition
-- (`pf._unsafe_rec`; the kernel's `pf` is an opaque constant).
partial def pf (n : Nat) : Nat :=
  let _again : Nat → Nat := pf
  if n == 7 then False.elim sorry else n

def viaPartial : Nat := pf 0

-- A `@[csimp]` theorem proved with `sorry`: the compiled code of `rC` runs
-- `stepG 0 = 0`, while `step_pos` is a true proof about `stepF 0 = 1`.
def stepF (n : Nat) : Nat := n + 1
def stepG (_ : Nat) : Nat := 0
@[csimp] theorem stepF_eq : @stepF = @stepG := sorry

def rC : Std.Legacy.Range := { stop := 0, step := stepF 0, step_pos := Nat.succ_pos 0 }

def spinC : Nat := Id.run do
  let mut s := 0
  for i in rC do
    s := s + i
  return s

-- The same with a `local` `@[csimp]` (saved nowhere: found by its
-- statement's shape, `programCsimps`).
def stepF2 (n : Nat) : Nat := n + 1
def stepG2 (_ : Nat) : Nat := 0
theorem stepF2_eq : @stepF2 = @stepG2 := sorry
attribute [local csimp] stepF2_eq

def rL : Std.Legacy.Range := { stop := 0, step := stepF2 0, step_pos := Nat.succ_pos 0 }

-- An `implemented_by` whose target computes another value (no axiom at
-- all): the compiled code of `rI` runs `stepImplI 0 = 0`.
def stepImplI (_ : Nat) : Nat := 0
@[implemented_by stepImplI] def stepI (n : Nat) : Nat := n + 1

def rI : Std.Legacy.Range := { stop := 0, step := stepI 0, step_pos := Nat.succ_pos 0 }

def spinI : Nat := Id.run do
  let mut s := 0
  for i in rI do
    s := s + i
  return s

-- Only the standard axioms (`Classical.em` uses `Classical.choice`): left out.
theorem usesChoice : 3 < 4 := by
  have _ := Classical.em True
  decide

def classical : Fin 4 := ⟨3, usesChoice⟩

def main : IO Unit := IO.println "main ran"
