/-! Runtime test: `Runtime.markPersistent`, `Runtime.markMultiThreaded`,
`Runtime.forget` and `Runtime.hold` at a string, a structure, a big Nat and
an array, and through a function generic in the value's type (review of
deptypes-cleanup, F2). The four externs are generic `BaseIO` actions; the
runtime's primitives are generic prelude functions
(`fn l2r_runtime_mark_persistent<T>(a : T) -> T`,
`fn l2r_runtime_forget<T>(a : T) -> L2RUnit`). With rule 1 the field of the
IO result is a `Box`, and lean2rr took the primitive's result to be of that
type: rrc rejected every call (`expected 'LAny', found 'LStr'` for a mark
at a string, `found 'L2RUnit'` for forget and hold). The result now has
the type of the argument (the marks) or `L2RUnit` (forget, hold), boxed
into the IO result. -/

structure P where
  a : Nat
  b : String

/-- The marks at a type parameter: the argument is a `Box`. -/
@[noinline] unsafe def markBoth {α : Type} (x : α) : IO α := do
  let y ← Runtime.markPersistent x
  Runtime.markMultiThreaded y

@[noinline] def dropBoth {α : Type} (x : α) : IO Unit := do
  Runtime.hold x
  Runtime.forget x

unsafe def main (args : List String) : IO Unit := do
  let n := args.length + 3
  -- A string.
  let s ← Runtime.markPersistent s!"s{n}"
  let s ← Runtime.markMultiThreaded s
  IO.println s
  -- A structure.
  let p ← Runtime.markPersistent ({ a := n, b := s!"p{n}" } : P)
  let p ← Runtime.markMultiThreaded p
  IO.println s!"{p.a} {p.b}"
  -- A big Nat.
  let k ← Runtime.markPersistent (n * 2 ^ 70)
  let k ← Runtime.markMultiThreaded k
  IO.println k
  -- An array.
  let a ← Runtime.markPersistent (Array.range n)
  let a ← Runtime.markMultiThreaded a
  IO.println a
  -- Hold borrows its argument; forget consumes it.
  Runtime.hold s
  Runtime.hold p
  Runtime.hold k
  Runtime.hold a
  IO.println s!"{s} {p.b} {k} {a.size}"
  Runtime.forget s!"f{n}"
  Runtime.forget ({ a := n + 1, b := s!"q{n}" } : P)
  Runtime.forget (n * 2 ^ 80)
  Runtime.forget (Array.range (n + 1))
  -- Through a generic function.
  let s2 ← markBoth s!"g{n}"
  let p2 ← markBoth ({ a := n + 2, b := s!"r{n}" } : P)
  let k2 ← markBoth (n * 2 ^ 90)
  let a2 ← markBoth (Array.range (n + 2))
  IO.println s!"{s2} {p2.a} {p2.b} {k2} {a2}"
  dropBoth s2
  dropBoth p2
  dropBoth k2
  dropBoth a2
  IO.println "done"
