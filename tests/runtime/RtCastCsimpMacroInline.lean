/-! Runtime test (`programCasts`, review of the walk's `@[csimp]` fix): a
global `@[csimp]` replaces `Decidable.casesOn` by `myCases`, which is
implemented by an inlined `unsafe` cast of a `P1` payload (read from a list,
so a box) to the result type, `P2`. Natively the same object is read. The
program mentions `Decidable.casesOn` only through Lean's `@[macro_inline]`
`ite`: Lean expands `ite` to `h.casesOn …` and then applies the
replacement (ToLCNF). The walk reached `ite`, a library constant whose value
it does not enter, never `Decidable.casesOn`, so it did not take `myCases`:
the program counted as one that cannot cast, and the program lean2rr built
stopped with "INTERNAL PANIC: unreachable code has been reached". Every
`@[csimp]` replacement that is a declaration of the program is now a root
of the walk (`programCsimps`). -/

structure P1 where
  x : Nat
  s : String

structure P2 where
  y : Nat
  t : String

structure Pkg where
  α : Type
  v : α

@[noinline] def mk (n : Nat) : Pkg := ⟨P1, ⟨n + 5, "one"⟩⟩
@[noinline] def pkgs (n : Nat) : List Pkg := [mk n, mk 3]
/-- A `Pkg` read from a list: its payload is a box. -/
@[noinline] def fetch (n : Nat) : Pkg := (pkgs n).headD (mk 0)

@[inline] unsafe def myCasesImpl.{u} {p : Prop} {motive : Decidable p → Sort u} (t : Decidable p)
    (_e : (h : ¬p) → motive (isFalse h)) (_tt : (h : p) → motive (isTrue h)) : motive t :=
  unsafeCast (fetch 3).v

@[implemented_by myCasesImpl] def myCases.{u} {p : Prop} {motive : Decidable p → Sort u} (t : Decidable p)
    (e : (h : ¬p) → motive (isFalse h)) (tt : (h : p) → motive (isTrue h)) : motive t :=
  Decidable.casesOn t e tt

@[csimp] theorem casesOn_eq.{u} : @Decidable.casesOn.{u} = @myCases.{u} := rfl

def main (args : List String) : IO Unit := do
  let q : P2 := if args.length = 7 then ⟨1, "a"⟩ else ⟨2, "b"⟩
  IO.println s!"{q.y} {q.t}"
