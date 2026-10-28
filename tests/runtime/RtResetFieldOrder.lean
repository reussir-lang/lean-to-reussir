/-! Runtime test: a documented difference in the order of releases in one
free (plan §10, "Order of releases in one free"; second hunt of the
release order). A value whose cell is rebuilt in place (Lean's
reset/reuse, Reussir's token reuse) releases the fields the code does not
read. Natively `expandResetReuse`'s fast path releases them last field
first (`BA`); lean2rr releases them in field order (`AB`).
`RtResetFieldOrder.native.out` is native's output,
`RtResetFieldOrder.l2r.out` lean2rr's. -/

def hnd (p : System.FilePath) (tag : String) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk p .append
  h.putStr tag
  return h

def fresh (name : String) : IO System.FilePath := do
  let p : System.FilePath := s!"resetfieldorder-{name}.txt"
  IO.FS.writeFile p ""
  return p

structure P where
  a : IO.FS.Handle
  b : IO.FS.Handle
  n : Nat

/-- `p`'s cell is reused; its fields `a`, `b` are not read. -/
@[noinline] def bump (p : P) (c : IO.FS.Handle) : IO P := pure ⟨c, c, p.n + 1⟩

@[noinline] def structReuse (path : System.FilePath) : IO Unit := do
  let p : P := ⟨← hnd path "A", ← hnd path "B", 0⟩
  let c ← hnd path "C"
  let q ← bump p c
  IO.println s!"struct: {← IO.FS.readFile path} n={q.n}"

inductive Q where
  | two (a b : IO.FS.Handle) (n : Nat)
  | nil

@[noinline] def stepQ (path : System.FilePath) (q : Q) (c : IO.FS.Handle) : IO Q := do
  match q with
  | .two _ _ n => IO.println s!"  in arm: {← IO.FS.readFile path}"; pure (.two c c (n + 1))
  | .nil => pure .nil

@[noinline] def inductiveReuse (path : System.FilePath) : IO Unit := do
  let q := Q.two (← hnd path "A") (← hnd path "B") 0
  let c ← hnd path "C"
  let q' ← stepQ path q c
  let n := match q' with | .two _ _ n => n | .nil => 0
  IO.println s!"inductive: {← IO.FS.readFile path} n={n}"

def main : IO Unit := do
  for (n, act) in [("struct", structReuse), ("inductive", inductiveReuse)] do
    let p ← fresh n
    act p
    IO.println s!"  {n} end: {← IO.FS.readFile p}"
    IO.FS.removeFile p
