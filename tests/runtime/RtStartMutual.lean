/-! Runtime test: startup order in `mutual` blocks whose members do not call
each other. The kernel records them as separate definitions; natively the
helpers of all members come first (those of later members first), then the
members in order. lean2rr finds such a block in the order in which Lean
compiled the module (a later member's helper compiled before an earlier
member's code). -/
def t (s : String) (n : Nat) : Nat := dbgTrace s fun _ => n

def a0 : Nat := t "a0" 0

mutual
def m1 : Nat := t "m1" (mh + 1)
where mh : Nat := t "m1.mh" 6
def m2 : Nat := t "m2" (m2h + 1)
where m2h : Nat := t "m2.m2h" 7
end

def a1 : Nat := t "a1" 1

-- Three members; the first has no helper.
mutual
def n1 : Nat := t "n1" 1
def n2 : Nat := t "n2" (n2h + 1)
where n2h : Nat := t "n2.n2h" 2
def n3 : Nat := t "n3" (n3a + n3b)
where
  n3a : Nat := t "n3.n3a" 3
  n3b : Nat := t "n3.n3b" 4
end

def a2 : Nat := t "a2" 2

-- A member that uses a later member (only possible in a `mutual` block).
mutual
def f1 : Nat := t "f1" (f2 + f1h)
where f1h : Nat := t "f1.f1h" 1
def f2 : Nat := t "f2" (f2h + 1)
where f2h : Nat := t "f2.f2h" 2
end

def a3 : Nat := t "a3" 3

-- Functions whose `where` helpers are constants.
mutual
def g1 (n : Nat) : Nat := n + g1h
where g1h : Nat := t "g1.g1h" 1
def g2 (n : Nat) : Nat := n + g2h
where g2h : Nat := t "g2.g2h" 2
end

-- An instance and a definition in one block.
class C (α : Type) where
  c : Nat

mutual
instance instCNat : C Nat where
  c := t "instCNat" ih
where ih : Nat := t "instCNat.ih" 1
def afterInst : Nat := t "afterInst" (aih + 1)
where aih : Nat := t "afterInst.aih" 2
end

def a4 : Nat := t "a4" 4

-- Constants whose calls Lean's closed-term extraction leaves in place (the
-- callee's type is not syntactically a function): Lean records no
-- compilation order for them, but a member that uses a later one shows the
-- block (only `mutual` allows such a use), here around a recursive pair.
def F := Nat → Nat
@[noinline] def gc1 : F := fun n => t "c1" n
@[noinline] def gc1_h1 : F := fun n => t "c1.h1" n
@[noinline] def gc2 : F := fun n => t "c2" n

mutual
def r1 : Nat → Nat
  | 0 => c1 + c2
  | n + 1 => r2 n
def c1 : Nat := gc1 h1
where h1 : Nat := gc1_h1 1
def r2 : Nat → Nat
  | 0 => c2
  | n + 1 => r1 n
def c2 : Nat := gc2 2
end

def main : IO Unit := do
  IO.eprintln "main"
  IO.println s!"{a0} {m1} {m2} {a1} {n1} {n2} {n3} {a2} {f1} {f2} {a3} {g1 1} {g2 2} {C.c Nat} {afterInst} {a4} {r1 3}"
