/-! Runtime test (review of the runtime's speed items): boxes of program
payloads made and released by `initialize` actions and startup constants,
before `main` (the program's releases are installed before the
initializers run, `any::init_releases`): a list of structures in a
reference, handles closed in native's order inside an initializer, a task's
result, a constant list. -/

structure Two (α : Type) where
  a : α
  b : α

def path : System.FilePath := "init-boxes-tmp.txt"

@[noinline] def openW (tag : String) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk path .append
  h.putStr tag
  pure h

initialize r1 : IO.Ref (List (Two String)) ← do
  let l : List (Two String) := [⟨"x", "y"⟩, ⟨"z", "w"⟩]
  let r ← IO.mkRef l
  r.set []
  r.set [⟨"p", "q"⟩]
  pure r

initialize closedOrder : String ← do
  IO.FS.writeFile path ""
  let h1 ← openW "1"; let h2 ← openW "2"; let h3 ← openW "3"; let h4 ← openW "4"
  let r ← IO.mkRef (#[some (Two.mk h1 h2), none, some (Two.mk h3 h4)] : Array (Option (Two IO.FS.Handle)))
  r.set #[]
  let s ← IO.FS.readFile path
  IO.FS.writeFile path ""
  pure s

instance : Nonempty (Two Nat) := ⟨⟨0, 0⟩⟩

initialize tk : Task (Except IO.Error (Two Nat)) ← IO.asTask (pure (Two.mk 3 4))

def startup : List (Two Nat) := (List.range 2000).map fun i => ⟨i, i + 1⟩

initialize firstSum : Nat ← pure (startup.foldl (fun s t => s + t.a + t.b) 0)

def main : IO Unit := do
  IO.println s!"r1 {(← r1.get).map (·.a)}"
  IO.println s!"closed {closedOrder}"
  IO.println s!"task {match tk.get with | .ok v => v.a + v.b | .error _ => 0}"
  IO.println s!"startup {firstSum} {startup.length}"
  r1.set []
  IO.FS.removeFile path
  IO.println "done"
