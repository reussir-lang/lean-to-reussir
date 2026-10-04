/-! Runtime test: updates of containers whose element type depends on a value
(review RV9C-02). A column `data : Array ty.denote` has the mono type
`Array lcAny`; Lean uses it at `Array Nat` in the branch where `ty = .nat`.
lean2rr converted the whole array to `Array Nat` for each `push`, `set!`,
`pop` or read, and the result back to `Array lcAny` to store it: two copies
per update, quadratic in a loop (40000 pushes: 7.7 s for 0.00 s natively).
The optimization `uniform-updates` runs these operations on the uniform
array, boxing or unboxing the single element; a `List ty.denote` cons is
built at `List lcAny`. The output is checked here; that no conversion runs
per update is checked by tests/runtime/conv-count-check.sh, which runs this
program at two sizes in a build that counts the conversions. -/

inductive Col | r | g | b deriving Repr, BEq, Inhabited

inductive Ty | nat | str | col | flt
deriving BEq, Repr

@[reducible] def Ty.denote : Ty → Type
  | .nat => Nat
  | .str => String
  | .col => Col
  | .flt => Float

structure Column where
  ty : Ty
  data : Array ty.denote

structure LColumn where
  ty : Ty
  data : List ty.denote

def Column.push (c : Column) (i : Nat) : Column :=
  match c with
  | ⟨.nat, d⟩ => ⟨.nat, d.push (i * 2^62)⟩
  | ⟨.str, d⟩ => ⟨.str, d.push s!"s{i}"⟩
  | ⟨.col, d⟩ => ⟨.col, d.push (if i % 3 == 0 then .r else if i % 3 == 1 then .g else .b)⟩
  | ⟨.flt, d⟩ => ⟨.flt, d.push (i.toFloat / 4)⟩

-- A read and a write of one element, a pop and a swap per step.
def Column.touch (c : Column) (i : Nat) : Column :=
  match c with
  | ⟨.nat, d⟩ => ⟨.nat, (d.set! (i % d.size) (d[i % d.size]! + 1)).swapIfInBounds 0 1⟩
  | ⟨.str, d⟩ => ⟨.str, d.set! (i % d.size) (d[i % d.size]! ++ "!")⟩
  | ⟨.col, d⟩ => ⟨.col, (d.push d[i % d.size]!).pop⟩
  | ⟨.flt, d⟩ => ⟨.flt, d.set! (i % d.size) (d[i % d.size]! * 2)⟩

def Column.summary (c : Column) : String :=
  match c with
  | ⟨.nat, d⟩ => s!"nat {d.size} {d.foldl (· + ·) 0}"
  | ⟨.str, d⟩ => s!"str {d.size} {d.foldl (fun a s => a + s.length) 0} {d.back?}"
  | ⟨.col, d⟩ => s!"col {d.size} {(d.filter (· == .g)).size} {reprStr d.back?}"
  | ⟨.flt, d⟩ => s!"flt {d.size} {d.foldl (· + ·) 0}"

def LColumn.push (c : LColumn) (i : Nat) : LColumn :=
  match c with
  | ⟨.nat, d⟩ => ⟨.nat, i :: d⟩
  | ⟨.str, d⟩ => ⟨.str, toString i :: d⟩
  | ⟨.col, d⟩ => ⟨.col, .b :: d⟩
  | ⟨.flt, d⟩ => ⟨.flt, i.toFloat :: d⟩

def LColumn.summary (c : LColumn) : String :=
  match c with
  | ⟨.nat, d⟩ => s!"lnat {d.length} {d.foldl (· + ·) 0}"
  | ⟨.str, d⟩ => s!"lstr {d.length} {d.head?}"
  | ⟨.col, d⟩ => s!"lcol {d.length}"
  | ⟨.flt, d⟩ => s!"lflt {d.length} {d.foldl (· + ·) 0}"

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3000
  let mut cols : Array Column := #[⟨.nat, #[]⟩, ⟨.str, #[]⟩, ⟨.col, #[]⟩, ⟨.flt, #[]⟩]
  for i in [0:n] do
    cols := cols.map (·.push i)
  for i in [0:n] do
    cols := cols.map (·.touch i)
  IO.println s!"{cols.map Column.summary}"
  let mut lcols : Array LColumn := #[⟨.nat, []⟩, ⟨.str, []⟩, ⟨.col, []⟩, ⟨.flt, []⟩]
  for i in [0:n] do
    lcols := lcols.map (·.push i)
  IO.println s!"{lcols.map LColumn.summary}"
