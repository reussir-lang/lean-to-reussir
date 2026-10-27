/-! Runtime test: the release order at the start of a branch inside a join
point declared in a constructor's arm, with the optimization `jp-small` off
(`RtDropArmOrderJp.opts`), so that even a small join point is outlined
(J3) or kept as a structured join point: the scrutinee `r` keeps its
renumbering at the `match` there (`withCtorAlt`), so it is newer than `h1`
(bound after `r`; a call before the `match` keeps Lean's `pushProj` from
moving its binding into the arm), and when both die at the `else` start,
`r` goes first (`S1`). With the join point outlined, its function started
without the renumbering and gave `1S` (bug hunt hunt-combos, p2; plan
§5.8, "Release order at the start of a branch"). The default passes are
in `RtDropArmOrder` (`jpCut`). -/

def hnd (p : System.FilePath) (tag : String) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk p .append
  h.putStr tag
  return h

inductive R where
  | two (h : IO.FS.Handle) (n : Nat)
  | none

@[noinline] def mkR (p : System.FilePath) (tag : String) (b : Bool) : IO R :=
  if b then do pure (.two (← hnd p tag) 5) else pure .none

@[noinline] def keepR (r : R) : IO Unit := match r with
  | .two h _ => h.putStr "k"
  | .none => pure ()

/-- A small join point in the arm. -/
@[noinline] def jpSmall (p : System.FilePath) (b c d : Bool) : IO Unit := do
  let r ← mkR p "S" b
  let h1 ← hnd p "1"
  IO.println "  jpSmall"
  match r with
  | .two _ n =>
    let tag ← if d then do IO.print ""; pure "x" else pure "y"
    if c then IO.println s!"{n} {tag}"; keepR r; h1.putStr "x"
    else IO.println s!"  jpSmall else {tag}: {← IO.FS.readFile p}"
  | .none => h1.putStr "n"

/-- A larger one. -/
@[noinline] def jpLarge (p : System.FilePath) (b c d : Bool) (k : Nat) : IO Unit := do
  let r ← mkR p "S" b
  let h1 ← hnd p "1"
  IO.println "  jpLarge"
  match r with
  | .two _ n =>
    let tag ← if d then do IO.print ""; pure "x" else pure "y"
    IO.println s!"  jpLarge {tag} {k}"
    IO.println s!"  jpLarge {tag} {k + 1} {k * 3}"
    IO.println s!"  jpLarge {tag} {k + 2} {k * 4} {k * k}"
    if c then IO.println s!"{n}"; keepR r; h1.putStr "x"
    else IO.println s!"  jpLarge else: {← IO.FS.readFile p}"
  | .none => h1.putStr "n"

def fresh (name : String) : IO System.FilePath := do
  let p : System.FilePath := s!"droparmjp-{name}.txt"
  IO.FS.writeFile p ""
  return p

def report (name : String) : IO Unit := do
  IO.println s!"{name}: {← IO.FS.readFile s!"droparmjp-{name}.txt"}"
  IO.FS.removeFile s!"droparmjp-{name}.txt"

def main (args : List String) : IO Unit := do
  let b := args.isEmpty
  jpSmall (← fresh "sx") b (!b) b; report "sx"
  jpSmall (← fresh "sy") b (!b) (!b); report "sy"
  jpLarge (← fresh "lx") b (!b) b 3; report "lx"
