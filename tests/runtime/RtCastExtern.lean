/-! Runtime test: a cast through an `@[extern]` declaration bound to an
`@[export]` definition of another type, in a program with no `unsafe` code,
`sorry` or axiom of its own. Lean does not compare the types of an extern
and the definition exported under its symbol, so such a program can read a
value as another type than its own (plan §5.1, `programCasts`): here an
existential payload of one structure read as another of the same layout
(natively the same object). -/

structure Pkg where
  α : Type
  v : α

structure P1 where
  x : Nat
  s : String

structure P2 where
  y : Nat
  t : String
deriving Inhabited

@[export l2rtest_payload, noinline] def payload (p : Pkg) : p.α := p.v
@[extern "l2rtest_payload"] opaque payloadAsP2 (p : Pkg) : P2

@[noinline] def mk (n : Nat) : Pkg := ⟨P1, ⟨n + 5, "one"⟩⟩

def main (args : List String) : IO Unit := do
  let p : Pkg := mk args.length
  let q := payloadAsP2 p
  IO.println s!"{q.y} {q.t}"
