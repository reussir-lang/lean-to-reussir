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

-- The same layouts with calls that Lean's closed-term extraction leaves in
-- place (the callee's type is not syntactically a function), so that Lean
-- records no compilation order for these constants and only the structure
-- places them: `where` declarations separated by `;`, or shifted by an
-- attribute or a doc comment (which their ranges leave out).
def F := Nat → Nat
@[noinline] def gv_lr : F := fun n => t "v.lr" n
@[noinline] def gv_a : F := fun n => t "v.a" n
@[noinline] def gv_b : F := fun n => t "v.b" n
@[noinline] def gw_lr : F := fun n => t "w.lr" n
@[noinline] def gw_a : F := fun n => t "w.a" n
@[noinline] def gw_b : F := fun n => t "w.b" n
@[noinline] def gx_lr : F := fun n => t "x.lr" n
@[noinline] def gx_a : F := fun n => t "x.a" n
@[noinline] def gx_b : F := fun n => t "x.b" n
@[noinline] def gy_lr : F := fun n => t "y.lr" n
@[noinline] def gy_a : F := fun n => t "y.a" n
@[noinline] def gy_b : F := fun n => t "y.b" n

def v : Nat :=
  let rec lr : Nat := gv_lr 0
  lr + a + b
where a : Nat := gv_a 1; b : Nat := gv_b 2

def w : Nat :=
  let rec lr : Nat := gw_lr 0
  lr + a + b
where
  a : Nat := gw_a 1
  @[noinline] b : Nat := gw_b 2

def x : Nat :=
  let rec lr : Nat := gx_lr 0
  lr + a + b
where
  /-- a doc comment -/ a : Nat := gx_a 1
  b : Nat := gx_b 2

def y : Nat :=
  let rec lr : Nat := gy_lr 0
  lr + a + b
where a : Nat := gy_a 1
      b : Nat := gy_b 2

class K (α : Type) where
  k : Nat

instance : K Nat where
  k :=
    let rec lk : Nat := t "inst.lk" 5
    lk + hk
where hk : Nat := t "inst.hk" 6

def main : IO Unit := do
  IO.eprintln "main"
  IO.println s!"{p} {q} {r} {s} {u} {v} {w} {x} {y} {K.k Nat}"
