/-! Runtime test: closed terms as Lean's closed-term extraction makes them.
Lean extracts a module's closed terms in compilation order with a cache of
the terms made so far, so a declaration with a term equal to an earlier
one's reads the earlier one's: the earlier one decides the order in which
the shared terms are evaluated (Lean evaluates a pair's fields in reverse
order), and the later one keeps the calls the extraction left dead (they
still run), not the dead reads of closed terms. `@[never_extract]` functions are not extracted, and a
declaration compiled with `set_option compiler.extract_closed false in`
evaluates its terms at each call, also in an instance of a polymorphic
one. -/

def t (s : String) (n : Nat) : Nat := dbgTrace s fun _ => n

-- The callee's type is not syntactically a function: Lean does not
-- extract the call on its own, only inside a larger term.
def F := Nat → Nat
@[noinline] def gZ : F := fun n => t "gz" n

def a : Nat × Nat := (t "x" 1, t "y" 2)
def b : Nat × Nat := (t "x" 1, t "y" 2)

def c : Nat := t "c" (gZ 1)
def d : Nat := t "c" (gZ 1)

structure S where
  x : Nat := t "S.x default" 1
  y : Nat := t "S.y default" 2

def s0 : S := {}
def s1 : S := { x := t "s1.x" 3 }

-- A function reading a constant's closed term.
def f (n : Nat) : Nat := n + t "x" 1

-- A function owns a pair's closed terms; the constant after it keeps dead
-- reads of the field terms, which Lean drops (only the pair is forced,
-- its fields in reverse order).
@[noinline] def fp (_ : Nat) : Nat × Nat := (t "u" 1, t "v" 2)
def pq : Nat × Nat := (t "u" 1, t "v" 2)

set_option compiler.extract_closed false in
def g (n : Nat) : Nat := n + t "g" 1

set_option compiler.extract_closed false in
@[noinline] def gp [ToString α] (x : α) : String := toString x ++ toString (t "gp" 1)

@[never_extract, noinline] def ne (n : Nat) : Nat := t "never_extract" n
def h (n : Nat) : Nat := n + ne 5

def main : IO Unit := do
  IO.eprintln "main"
  IO.println s!"{a} {b} {c} {d} {s0.x} {s0.y} {s1.x} {s1.y} {pq} {fp 0}"
  IO.println s!"{f 1} {f 2} {g 1} {g 2} {gp 1} {gp "z"} {gp 3} {h 1} {h 2}"
