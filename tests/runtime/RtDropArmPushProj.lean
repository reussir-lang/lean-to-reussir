/-! Runtime test: a documented difference in the release order at the
start of a branch (plan §10, "Release order at the start of a branch";
review of the arm release order). The arm of `.two` reads `n` only in the
`then` branch of the `if` that follows at once. Natively Lean's `pushProj`
moves the projection of `n` into that branch, so the scrutinee `r`, which
holds handle `S` in a field the arm does not read, stays live into the
`if`: in the `then` branch it is released after the branch's own release
(`h1`) and after the projection (`1S`), in the `else` branch at its start
(`S1x`). lean2rr releases `r` at the arm's start, after it takes `n`
(`S1` in the `then` branch). `RtDropArmPushProj.native.out` is native's
output, `RtDropArmPushProj.l2r.out` lean2rr's. -/

def hnd (p : System.FilePath) (tag : String) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk p .append
  h.putStr tag
  return h

inductive R where
  | two (h : IO.FS.Handle) (n : Nat)
  | none

@[noinline] def mkR (p : System.FilePath) (b : Bool) : IO R :=
  if b then do pure (.two (← hnd p "S") 5) else pure .none

@[noinline] def pushNested (p : System.FilePath) (b c : Bool) : IO Unit := do
  let r ← mkR p b
  let h1 ← hnd p "1"
  match r with
  | .two _ n =>
    if c then IO.println s!"  pushNested then {n}: {← IO.FS.readFile p}"
    else h1.putStr "x"; IO.println s!"  pushNested else: {← IO.FS.readFile p}"
  | .none => h1.putStr "n"

def fresh (name : String) : IO System.FilePath := do
  let p : System.FilePath := s!"droparmpp-{name}.txt"
  IO.FS.writeFile p ""
  return p

def report (name : String) : IO Unit := do
  IO.println s!"{name}: {← IO.FS.readFile s!"droparmpp-{name}.txt"}"
  IO.FS.removeFile s!"droparmpp-{name}.txt"

def main (args : List String) : IO Unit := do
  let b := args.isEmpty
  pushNested (← fresh "t") b true; report "t"
  pushNested (← fresh "e") b false; report "e"
