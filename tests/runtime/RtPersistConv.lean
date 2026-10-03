/-! Runtime test: a closed term whose tasks are held at another
representation (in an existential, so uniform code holds converted copies
of the typed tasks): the walk knows each copy by its original's identity,
so its first pass collects it instead of forcing it, and the tasks run in
the order the native workers take them (here the order they were created
in). One worker thread (`RtPersistConv.pipe`). From review round 7, area
L, round 4 (code reading next to RV7L-07). -/
structure Ex where
  α : Type
  t : Task α
  fmt : α → String

@[noinline] def mkEx (_ : Unit) : Array Ex :=
  let a := Task.spawn fun _ => dbgTrace "ex: nat (created first)" fun _ => (1 : Nat)
  let b := Task.spawn fun _ => dbgTrace "ex: string (created second)" fun _ => "s"
  let c := Task.spawn fun _ => dbgTrace "ex: nat 2 (created third)" fun _ => (3 : Nat)
  #[⟨Nat, a, toString⟩, ⟨String, b, id⟩, ⟨Nat, c, toString⟩]

@[noinline] def mapEx (_ : Unit) : List Ex :=
  (List.range 3).map fun i => ⟨Nat, Task.spawn fun _ => dbgTrace s!"mapEx: {i}" fun _ => i, toString⟩

@[noinline] def mkEx2 (n : Nat) : Array Ex :=
  let a := Task.spawn fun _ => dbgTrace "ex2: first" fun _ => n
  let b := Task.spawn fun _ => dbgTrace "ex2: second" fun _ => s!"{n}"
  let c := Task.spawn fun _ => dbgTrace "ex2: third" fun _ => n + 1
  #[⟨Nat, a, toString⟩, ⟨String, b, id⟩, ⟨Nat, c, toString⟩]

@[noinline] def showEx (e : Ex) : String := e.fmt e.t.get

def main : IO Unit := do
  let busy ← IO.asTask (do IO.sleep 50; return 1)
  IO.eprintln "main"
  let es := mkEx ()
  IO.eprintln s!"ex {es.size}"
  IO.eprintln s!"values {es.map showEx}"
  let ms := mapEx ()
  IO.eprintln s!"mapEx {ms.map showEx}"
  let e2 := mkEx2 5
  IO.eprintln s!"ex2 {e2.map showEx}"
  let _ ← IO.wait busy
