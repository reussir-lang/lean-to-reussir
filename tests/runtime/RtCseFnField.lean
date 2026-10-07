/-! Runtime test: a call that Lean's mono `cse` merges across types whose
value holds a function inside a structure (review of XT-6 round 2,
rv7/frontend/xt6/round2 XT6-03). A check that saw only the arrows written in
the result type let `Fns α` and `Sink α`, which hide them in a field, be
aligned to the earlier type, and the closure in the field, used at the other
type with an argument of that type, needed a conversion that does not exist
("no representation conversion from Nat to LStr"): "INTERNAL PANIC:
unreachable code has been reached". `Mono.serves` follows the inductives
into their fields, so the calls are not aligned to the earlier call's
instance; they go to the instance at `lcAny`, whose closures serve both
types (their traces are in the closures, which run per application in
both). -/

@[noinline] def tagger {α : Type} (n : Nat) (x : α) : α := dbgTrace s!"tag {n}" fun _ => x

structure Fns (α : Type) where
  run : α → α
  name : String

@[noinline] def mkFns {α : Type} (n : Nat) : Fns α := ⟨tagger n, s!"fns {n}"⟩

structure Sink (α : Type) where
  put : α → Nat

@[noinline] def countSink {α : Type} (k : Nat) : Sink α := ⟨fun _ => k⟩

def fns (n : Nat) : String :=
  let a : Fns Nat := mkFns n
  let b : Fns String := mkFns n
  s!"{a.name} {a.run 5} {b.name} {b.run "s"}"

def sinks (k : Nat) : Nat :=
  let a : Sink Nat := countSink k
  let b : Sink String := countSink k
  a.put 1 + b.put "x"

def main (args : List String) : IO Unit := do
  IO.println s!"sinks {sinks (args.length + 3)}"
  IO.println s!"fns {fns args.length}"
