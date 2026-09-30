/-! Runtime test: a pending thunk or task stored in a structure that crosses
between typed and uniform code (an existential) in a loop keeps one cell:
converting back gives the original cell, so memory stays flat, and the
computation still runs once. -/

structure TW (α : Type) where
  t : Thunk α
  tag : Nat

structure PK where
  keep : {α : Type} → TW α → TW α

structure TK where
  keep : {α : Type} → Task α → Task α

@[noinline] def loop (p : PK) (n : Nat) (seed : Nat) : Nat := Id.run do
  let mut g : TW Nat := ⟨Thunk.mk (fun _ => dbgTrace "thunk forced" fun _ => seed * 2), 7⟩
  for _ in [0:n] do
    g := p.keep g
  return g.t.get + g.t.get + g.tag

@[noinline] def loopTask (p : TK) (n : Nat) (t : Task (Except IO.Error Nat)) : Task (Except IO.Error Nat) := Id.run do
  let mut g := t
  for _ in [0:n] do
    g := p.keep g
  return g

def main (args : List String) : IO Unit := do
  let n := 2000000 + args.length
  IO.println s!"loop {loop ⟨fun w => w⟩ n args.length}"
  let t ← IO.asTask (do IO.sleep 20; IO.println "io task runs"; return 5)
  let g := loopTask ⟨fun w => w⟩ n t
  IO.println s!"task {match ← IO.wait g with | .ok v => v | .error _ => 0}"
  IO.println s!"finished after wait: {← IO.hasFinished t} {← IO.hasFinished g}"
