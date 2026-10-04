/-! Runtime test: placeholders (`box(0)` natively, lean2rr's `zeroValue`) of
types whose first constructor with fields has no finite value through
another type, although a later constructor does. `Array.map` (also to
another element type), `mapM`, `mapIdx` and `modify` store a placeholder in
the slot being updated, and `IO.Ref.modify` (also `StateRefT`'s `modify`)
leaves one in the reference while it updates it; such a placeholder must not
be `l2r_unreachable`.
From the round-9 review, area containers (RV9C-01). -/

-- The first constructor recurses through a pair; `var` is finite.
inductive Term where
  | app (p : Term × Term)
  | var (n : Nat)
deriving Repr

def Term.size : Term → Nat
  | .app (a, b) => a.size + b.size + 1
  | .var _ => 1

-- Mutual: `A.wrap` recurses through `B`, which has no other constructor.
mutual
inductive A where
  | wrap (b : B)
  | lit (n : Nat)
deriving Repr
inductive B where
  | mk (a : A) (tag : Nat)
deriving Repr
end

-- The first constructor holds a value of an empty type.
inductive W where
  | bad (e : Empty)
  | ok (n : Nat)

def W.val : W → Nat | .bad e => nomatch e | .ok n => n

-- A state that holds a `Term`.
structure St where
  cur : Term
  steps : Nat

def bump : StateRefT St IO Unit := modify fun s => { s with cur := .app (s.cur, .var s.steps), steps := s.steps + 1 }

def main : IO Unit := do
  let ts : Array Term := #[.var 1, .app (.var 2, .var 3)]
  IO.println s!"sizes {ts.map Term.size}"
  IO.println s!"map {repr (ts.map fun t => Term.app (t, .var 0))}"
  IO.println s!"modify {repr (ts.modify 1 fun t => .app (t, t))}"
  IO.println s!"mapIdx {repr (ts.mapIdx fun i t => if i == 0 then .var 9 else t)}"
  let m ← ts.mapM fun t => pure (Term.app (.var 5, t))
  IO.println s!"mapM {repr m}"
  let r ← IO.mkRef (Term.var 7)
  r.modify fun t => .app (t, t)
  IO.println s!"ref {repr (← r.get)}"
  let as : Array A := #[.lit 1, .wrap ⟨.lit 2, 3⟩]
  IO.println s!"mutual {repr (as.map fun a => A.wrap ⟨a, 0⟩)}"
  let ws : Array W := #[.ok 1, .ok 2]
  IO.println s!"empty {(ws.map fun w => W.ok (w.val + 1)).map W.val}"
  let ((), s) ← bump.run { cur := .var 0, steps := 1 }
  IO.println s!"state {repr s.cur} {s.steps}"
