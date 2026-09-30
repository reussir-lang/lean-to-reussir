/-! Runtime test: startup order of `where`/`let rec` helper constants and of
the specializations made for their declaration. Lean compiles a declaration
after its helpers (one component of their reference graph at a time,
callees first), so its initializer runs the helpers first, then the
specializations made while compiling the declaration, then the declaration
itself. -/

@[specialize] def gen {m : Type → Type} [Monad m] (f : Nat → m Nat) : m Nat := f 1

def t (s : String) (n : Nat) : Nat := dbgTrace s fun _ => n

def a0 : Nat := t "a0" 0

-- A helper constant and a specialization made in the parent.
def c : Nat := dbgTrace "c" fun _ => Id.run (gen (m := Id) (fun i => dbgTrace "spec in c" fun _ => pure i)) + helper
where helper : Nat := t "c.helper" 2

-- Several helpers, one needing another that comes later in the source.
def p : Nat := t "p" (h1 + h2)
where
  h1 : Nat := t "p.h1" 1
  h2 : Nat := t "p.h2" (h3 + 1)
  h3 : Nat := t "p.h3" 3

-- A helper constant used through a helper function.
def q : Nat := t "q" (outer 2)
where
  outer (n : Nat) : Nat := n + inner
  inner : Nat := t "q.inner" 4

-- `let rec` inside a constant.
def lr : Nat := dbgTrace "lr" fun _ =>
  let rec k : Nat := t "lr.k" 5
  k + 1

-- A specialization made in a helper function: before the parent.
def s : Nat := t "s" (go 3)
where go : Nat → Nat
  | 0 => (gen (m := Option) (fun i => dbgTrace "spec in s.go" fun _ => some i)).getD 0
  | n + 1 => go n

-- Where-helper of an instance.
class K (α : Type) where
  k : Nat

instance : K Nat where
  k := t "inst.k" hk
where hk : Nat := t "inst.hk" 6

-- A helper of `main`, and a specialization made in `main`.
def main : IO Unit := do
  IO.eprintln "main"
  IO.println s!"{Id.run (gen (m := Id) (fun i => dbgTrace "spec in main" fun _ => pure i))} {a0} {c} {p} {q} {lr} {s} {K.k Nat} {later}"
where later : Nat := t "main.later" 7

def a1 : Nat := t "a1" 8
