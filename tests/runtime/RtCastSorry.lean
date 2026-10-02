/-! Runtime test: a cast through an equality proved by `sorry`, in a program
with no `unsafe` code of its own. Such a program can read a value as
another type than its own (plan §5.1, `programCasts`): an existential
payload of one structure read as another of the same layout converts
like an `unsafeCast`. -/

structure P1 where
  x : Nat
  s : String

structure P2 where
  y : Nat
  t : String

structure Pkg where
  α : Type
  v : α

theorem pkgIsP2 (p : Pkg) : p.α = P2 := sorry

@[noinline] def asP2 (p : Pkg) : P2 := cast (pkgIsP2 p) p.v

def main (args : List String) : IO Unit := do
  let p : Pkg := ⟨P1, ⟨args.length + 5, "one"⟩⟩
  let q := asP2 p
  IO.println s!"{q.y} {q.t}"
