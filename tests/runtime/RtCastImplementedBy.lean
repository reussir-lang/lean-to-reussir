/-! A safe `opaque` implemented by an `unsafe` library function makes the
program one that can cast (round 6 RV6T-05). No unsafe declaration, sorry,
axiom, extern or export of its own: an `opaque` implemented by Init's unsafe
`TypeName.mk` gives P1 and P2 TypeName
instances with the same name, so `Dynamic.get? P2` reads a P1 as a P2
(natively the same object). -/
structure P1 where
  x : Nat
  s : String

structure P2 where
  y : Nat
  t : String

@[implemented_by TypeName.mk] opaque mkTN (α : Type u) (typeName : Lean.Name) : TypeName α

instance : TypeName P1 := mkTN P1 `Same
instance : TypeName P2 := mkTN P2 `Same

@[noinline] def mk (n : Nat) : Dynamic := Dynamic.mk (P1.mk (n + 5) "one")

def main (args : List String) : IO Unit := do
  let d := mk args.length
  IO.println s!"{d.typeName}"
  match d.get? P2 with
  | some q => IO.println s!"{q.y} {q.t}"
  | none => IO.println "none"
