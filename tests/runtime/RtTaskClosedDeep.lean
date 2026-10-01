/-! Runtime test: a closed term waits, when it is first evaluated, for the
tasks it holds anywhere: captured by closures, in a thunk's computation
(without forcing the thunk), in a list, as Lean's `lean_mark_persistent`
does. (stderr shows the order.) -/
@[noinline] def mkClosures (n : Nat) : (Unit → Nat) × (Unit → Nat) :=
  let t := Task.spawn fun _ => dbgTrace s!"task in closures {n}" fun _ => n
  (fun _ => t.get, fun _ => t.get + 1)

@[noinline] def mkThunk (n : Nat) : Thunk Nat :=
  let t := Task.spawn fun _ => dbgTrace s!"task in thunk {n}" fun _ => n
  Thunk.mk fun _ => t.get + 1

@[noinline] def mkList (n : Nat) : List (Option (Task Nat)) :=
  [some (Task.spawn fun _ => dbgTrace s!"task in list {n}" fun _ => n), none]

@[noinline] def useF (f : (Unit → Nat) × (Unit → Nat)) (b : Bool) : IO Unit :=
  if b then IO.eprintln s!"{f.1 ()}" else IO.eprintln "have closures"
@[noinline] def useT (f : Thunk Nat) (b : Bool) : IO Unit :=
  if b then IO.eprintln s!"{f.get}" else IO.eprintln "have thunk"
@[noinline] def useL (f : List (Option (Task Nat))) (b : Bool) : IO Unit :=
  if b then IO.eprintln s!"{f.length}" else IO.eprintln "have list"

def main (args : List String) : IO Unit := do
  let b := args.length > 5
  let busy ← IO.asTask (do IO.sleep 50; return 1)
  IO.eprintln "start"
  useF (mkClosures 5) b
  useT (mkThunk 6) b
  useL (mkList 7) b
  let _ ← IO.wait busy
  IO.eprintln "end"
