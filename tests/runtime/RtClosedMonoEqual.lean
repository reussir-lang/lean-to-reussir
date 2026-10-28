/-!
Closed calls of one generic definition at type arguments whose mono types
are equal (`Fin 3`, `Fin 5`, `Nat` and a one-field structure over `Nat`),
each in its own declaration. Natively `mk` is one function and Lean's
closed-term cache compares mono terms, in which type arguments are erased
and `Option (Fin 3)`, `Option W` are `Option Nat`: the four calls are one
closed term, `mk ◾ 5 : Option Nat`, and `mk 5` is traced once. Stage 1
gives the calls instances at `Fin 3`, `Nat` and `W` (three identical
instances), and the cache keyed on their names made three closed terms:
three traces. Now `extractLikeLean` also caches a term under its
instances' declarations and the mono images of their type arguments
(`closedMonoKey`). A bug hunt of the extern routing (repro R3a). Also a
type parameter that is `lcAny` in both instances (`mk2`'s hidden `α`), and
a term in an instance of a generic declaration, which natively is generic
code and does not share the concrete declaration's term (`gen`, `user`).
-/

@[noinline] def mk {α : Type} (n : Nat) : Option α := dbgTrace s!"mk {n}" fun _ => none

structure W where
  x : Nat

@[noinline] def p1 (k : Nat) : Nat := match (mk 5 : Option (Fin 3)) with | some x => x.val | none => k
@[noinline] def p2 (k : Nat) : Nat := match (mk 5 : Option (Fin 5)) with | some x => x.val + 1 | none => k + 1
@[noinline] def p3 (k : Nat) : Nat := match (mk 5 : Option Nat) with | some x => x | none => k + 2
@[noinline] def p4 (k : Nat) : Nat := match (mk 5 : Option W) with | some w => w.x | none => k + 3

-- A closed call at a type whose mono type differs (`String`): its own
-- closed term, natively too.
@[noinline] def p5 (k : Nat) : Nat := match (mk 5 : Option String) with | some s => s.length | none => k + 4

-- `α` shows nowhere in `mk2`'s type: every call takes it at `lcAny`
-- (`Mono.typeParamHidden`), which is the same in both instances; `β` is
-- `Fin 3` and `Nat`, one mono type: one closed term, one trace.
@[noinline] def mk2 {α β : Type} (n : Nat) : Option β := dbgTrace s!"mk2 {n}" fun _ => none
@[noinline] def q1 (k : Nat) : Nat := match (mk2 (α := String) 7 : Option (Fin 3)) with | some x => x.val | none => k + 5
@[noinline] def q2 (k : Nat) : Nat := match (mk2 (α := Bool) 7 : Option Nat) with | some x => x | none => k + 6

-- In generic code (`gen`), natively one function, the term is at
-- `Option lcAny`: natively a second closed term besides `user`'s at
-- `Option Nat`, two traces. `gen`'s instance at `W` has concrete types,
-- but does not share `user`'s term (`Pipeline.monoOwner`; review of the
-- bug hunt, repro V3b).
@[noinline] def mk3 {α : Type} (n : Nat) : Option α := dbgTrace s!"mk3 {n}" fun _ => none
@[noinline] def gen {α : Type} (k : Nat) (_o : Option α) : Nat := match (mk3 8 : Option α) with | some _ => 0 | none => k
@[noinline] def user (k : Nat) : Nat := match (mk3 8 : Option Nat) with | some _ => 1 | none => k + 1
@[noinline] def useW (k : Nat) : Nat := gen k (none : Option W) + 10

def main (args : List String) : IO Unit := do
  let k := args.length
  IO.println s!"{p1 k} {p2 k} {p3 k} {p4 k} {p5 k}"
  IO.println s!"{p4 (k + 1)} {p3 (k + 1)} {p5 (k + 1)}"
  IO.println s!"{q1 k} {q2 k} {q2 (k + 1)}"
  IO.println s!"{user k} {useW k}"
