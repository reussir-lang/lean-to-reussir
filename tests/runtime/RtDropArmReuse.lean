/-! Runtime test: the release order at the start of a branch where Lean
reuses the matched value's cell (plan §5.8, "Release order at the start of
a branch"; second hunt of the release order). A matched value that dies in
an arm whose code builds a constructor of the same size is not released at
the arm's start natively: Lean's `insertResetReuse` turns it into a
`reset` after the arm's prolog (the releases of the other values that die
there, newest first), which releases the fields the code does not read
(`expandResetReuse`). So the matched value goes last.
- `reuseArm`: the `.two` arm reads no field and builds a `.two`; `h1` dies
  there: `1S` (lean2rr gave `S1`). `reuseArm2`: two handles die there:
  `21S`.
- `twice`: `r` matched in both branches of an `if`, only the first
  match's `.two` arm builds a `.two`, so Lean resets `r` there only: `1S`
  there, and in the other match's `.two` arm `r` first (`CS1`, `c` dying
  at the `else` branch's start; the review found `C1S` when the two
  matches shared their `reset`s).
- `noReuseArm` (the arm builds no `.two`: Lean borrows `r`, its caller
  releases it) and `reuseArmRead` (the arm reads `n`) were already right.
- `ioThrow`: an IO result whose value (`h2`) only the `else` branch reads
  (Lean's `pushProj` moves its projection there); the `then` branch throws,
  which builds an `EST.Out.error` in the result's cell, so the `reset` of
  the result releases `h2` after the branch's prolog (`h1`): `12` (lean2rr
  gave `21`). `exceptThrow`: the same through `ExceptT String IO`. -/

def hnd (p : System.FilePath) (tag : String) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk p .append
  h.putStr tag
  return h

inductive R where
  | two (h : IO.FS.Handle) (n : Nat)
  | none

def tagOf : R → Nat | .two _ n => n | .none => 0

@[noinline] def mkR (p : System.FilePath) (b : Bool) : IO R :=
  if b then do pure (.two (← hnd p "S") 0) else pure .none

@[noinline] def reuseArm (r : R) (h1 c : IO.FS.Handle) : IO R := do
  match r with
  | .two _ _ => pure (.two c 1)
  | .none => pure (.two h1 2)

@[noinline] def reuseArm2 (r : R) (h1 h2 c : IO.FS.Handle) : IO R := do
  match r with
  | .two _ _ => pure (.two c 1)
  | .none => do h1.putStr "x"; pure (.two h2 2)

@[noinline] def twice (r : R) (h1 c : IO.FS.Handle) (b : Bool) : IO R := do
  if b then
    match r with
    | .two _ _ => pure (.two c 1)
    | .none => pure (.two h1 2)
  else
    match r with
    | .two _ _ => pure .none
    | .none => pure (.two h1 3)

@[noinline] def noReuseArm (r : R) (h1 : IO.FS.Handle) : IO R := do
  match r with
  | .two _ _ => pure .none
  | .none => pure (.two h1 2)

@[noinline] def reuseArmRead (r : R) (h1 c : IO.FS.Handle) : IO R := do
  match r with
  | .two _ n => pure (.two c (n + 1))
  | .none => pure (.two h1 2)

@[noinline] def ioThrow (p : System.FilePath) (b : Bool) : IO Unit := do
  let h1 ← hnd p "1"
  let h2 ← hnd p "2"
  if b then throw (IO.userError "stop")
  h1.putStr "a"; h2.putStr "b"

@[noinline] def exceptThrow (p : System.FilePath) (b : Bool) : ExceptT String IO Unit := do
  let h1 ← hnd p "1"
  let h2 ← hnd p "2"
  if b then throw "stop"
  h1.putStr "a"; h2.putStr "b"

def fresh (name : String) : IO System.FilePath := do
  let p : System.FilePath := s!"droparmreuse-{name}.txt"
  IO.FS.writeFile p ""
  return p

def report (name : String) (p : System.FilePath) : IO Unit := do
  IO.println s!"  {name} end: {← IO.FS.readFile p}"
  IO.FS.removeFile p

def main (args : List String) : IO Unit := do
  let b := args.isEmpty
  let p ← fresh "a"
  let r ← mkR p b
  let r' ← reuseArm r (← hnd p "1") (← hnd p "C")
  IO.println s!"reuseArm: {← IO.FS.readFile p} ({tagOf r'})"
  report "reuseArm" p
  let p ← fresh "a2"
  let r ← mkR p b
  let h1 ← hnd p "1"
  let h2 ← hnd p "2"
  let r' ← reuseArm2 r h1 h2 (← hnd p "C")
  IO.println s!"reuseArm2: {← IO.FS.readFile p} ({tagOf r'})"
  report "reuseArm2" p
  for c in [b, !b] do
    let p ← fresh "w"
    let r ← mkR p b
    let r' ← twice r (← hnd p "1") (← hnd p "C") c
    IO.println s!"twice {c}: {← IO.FS.readFile p} ({tagOf r'})"
    report "twice" p
  let p ← fresh "b"
  let r ← mkR p b
  let r' ← noReuseArm r (← hnd p "1")
  IO.println s!"noReuseArm: {← IO.FS.readFile p} ({tagOf r'})"
  report "noReuseArm" p
  let p ← fresh "d"
  let r ← mkR p b
  let r' ← reuseArmRead r (← hnd p "1") (← hnd p "C")
  IO.println s!"reuseArmRead: {← IO.FS.readFile p} ({tagOf r'})"
  report "reuseArmRead" p
  for c in [b, !b] do
    let p ← fresh "c"
    try ioThrow p c; IO.println s!"ioThrow {c} ok: {← IO.FS.readFile p}"
    catch e => IO.println s!"ioThrow {c} {e}: {← IO.FS.readFile p}"
    report "ioThrow" p
  for c in [b, !b] do
    let p ← fresh "x"
    match ← (exceptThrow p c).run with
    | .ok () => IO.println s!"exceptThrow {c} ok: {← IO.FS.readFile p}"
    | .error e => IO.println s!"exceptThrow {c} {e}: {← IO.FS.readFile p}"
    report "exceptThrow" p
