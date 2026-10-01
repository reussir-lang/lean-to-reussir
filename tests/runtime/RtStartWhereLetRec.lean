/-! Runtime test: startup order of a declaration's `where` helpers and the
`let rec`s of its body. Natively the `where` helpers come first (a `where`
clause is a `let rec` around the body), then the body's, then the nested
ones, although the `where` clause comes last in the source. -/
def t (s : String) (n : Nat) : Nat := dbgTrace s fun _ => n

def p : Nat :=
  let rec lr1 : Nat := t "p.lr1" 1
  let rec lr2 : Nat := t "p.lr2" 2
  lr1 + lr2 + w1 + w2
where
  w1 : Nat := t "p.w1" 3
  w2 : Nat := t "p.w2" 4

def q : Nat :=
  let rec lr : Nat := t "q.lr" 1
  lr + w
where w : Nat := t "q.w" 2

-- A `let rec` nested in a `where` helper, and one in the body.
def r : Nat :=
  let rec body : Nat := t "r.body" 1
  body + outer
where
  outer : Nat :=
    let rec inner : Nat := t "r.outer.inner" 2
    t "r.outer" (inner + 1)

-- Only `let rec`s.
def s : Nat :=
  let rec a : Nat := t "s.a" 1
  let rec b : Nat := t "s.b" 2
  a + b

-- Only `where` helpers.
def u : Nat := t "u" (h2 + h1)
where
  h1 : Nat := t "u.h1" 1
  h2 : Nat := t "u.h2" 2

class K (α : Type) where
  k : Nat

instance : K Nat where
  k :=
    let rec lk : Nat := t "inst.lk" 5
    lk + hk
where hk : Nat := t "inst.hk" 6

def main : IO Unit := do
  IO.eprintln "main"
  IO.println s!"{p} {q} {r} {s} {u} {K.k Nat}"
