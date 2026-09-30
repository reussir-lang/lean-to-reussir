/-! Runtime test: thunks and tasks of a concrete type stored where the type
is not statically known (an existential field, stored as `Box`): the
converted cell forces the original, so a thunk still runs once and an IO
task stays deferred. -/

@[noinline] def mk (tag : String) (v : Nat) : Thunk Nat :=
  Thunk.mk fun _ => dbgTrace s!"force {tag}" fun _ => v * 2

@[noinline] def mkT (v : Nat) : Task Nat := Task.spawn fun _ => v + 1

structure Pack where
  α : Type
  t : Thunk α
  shw : α → String

structure TPack where
  α : Type
  t : Task α
  shw : α → String

@[noinline] def usePack (p : Pack) : String := p.shw p.t.get ++ "/" ++ p.shw p.t.get
@[noinline] def useTPack (p : TPack) : String := p.shw p.t.get

def main (args : List String) : IO Unit := do
  let n := args.length
  let th := mk "shared" (n + 5)
  let p : Pack := ⟨Nat, th, toString⟩
  IO.println s!"{usePack p} {th.get} {usePack p}"
  let q : Pack := ⟨Nat, mk "q" 1, toString⟩
  IO.println s!"{th.get} {usePack q}"
  let tp : TPack := ⟨Nat, mkT n, toString⟩
  IO.println s!"{useTPack tp}"
  let io ← IO.asTask (do IO.sleep 50; IO.println "io task"; return n + 100)
  let tp2 : TPack := ⟨Except IO.Error Nat, io, fun r => match r with | .ok v => toString v | .error _ => "err"⟩
  IO.println "before use"
  IO.println s!"{useTPack tp2}"
