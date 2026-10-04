/-! A cast through an `@[extern]` declaration bound to an `@[export]`
definition of another type, in a program with no `unsafe` code, `sorry` or
axiom of its own. Lean does not compare the types of an extern and the
definition exported under its symbol, so natively such a program reads a
value as another type than its own: here an existential payload of one
structure read as another of the same layout (natively the same object).
lean2rr once bound the two and cast (review RV6T-01, plan §5.1,
`programCasts`). The binding of an extern's C symbol now needs one type and
one compiled signature (translation plan §5.8, "Externs of the program"), so it fails the
type test, and the extern has no Lean definition: lean2rr refuses the
program, naming the failed test. -/

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
