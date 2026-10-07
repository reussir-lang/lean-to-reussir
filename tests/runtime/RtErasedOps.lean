/-! Runtime test: the dependent-types page's `ops` example (rule 4). The
field `run : {α : Type} → List α → Nat` holds `List.length` and a lambda;
neither runs before its list arrives, so the function type has no
parameter for `α` at run time (`List_Box → Nat`), and neither has the
lambda's function (`ops_lam(xs)`). Applied at two element types and
through a function value bound at a type. `mkOp`'s lambda computes `c`
before its list parameter, but Lean eta-expands it to both parameters, so
`work` runs at each application to a list, natively too. -/

structure Op where
  run : {α : Type} → List α → Nat

def ops : List Op := [⟨List.length⟩, ⟨fun xs => dbgTrace s!"lam {xs.length}" fun _ => xs.length * 2⟩]

@[noinline] def bindAt (o : Op) : List String → Nat := @o.run String

@[noinline] def work (k : Nat) : Nat := dbgTrace s!"work {k}" fun _ => k * 2
@[noinline] def mkOp (k : Nat) : Op := ⟨fun {α} => let c := work k; fun (xs : List α) => xs.length + c⟩
@[noinline] def twice (g : List Nat → Nat) : Nat := g [1, 2] + g [3]

def main (args : List String) : IO Unit := do
  IO.println (ops.map (fun o => o.run [1, 2, 3]))
  IO.println (ops.map (fun o => o.run ["a", "b"]))
  IO.println (ops.map (fun o => bindAt o args + 10 * bindAt o ["x"]))
  let o := mkOp (args.length + 1)
  let g := @o.run Nat
  IO.println (twice g)
