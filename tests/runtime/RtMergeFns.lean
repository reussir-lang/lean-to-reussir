/-! Runtime test: instances of one definition at several types that lower
to the same Reussir function, merged by lean2rr's `merge-fns` (a copy
calls the first; calls of a copy call the first): `len`, self-recursive,
called directly and kept as a function value (partial applications in a
list, applied later), merges; `evens` and `odds`, mutually recursive, stay
apart (each one's code names the other); `rv` and the `List.reverse` and
`List.reverseAux` instances it calls, each called from one place, stay
apart (a function called from one place only takes no part: LLVM inlines
it there). -/

@[noinline] def len {α : Type} : List α → Nat → Nat
  | [], n => n
  | _ :: r, n => len r (n + 1)

mutual
@[noinline] def evens {α : Type} : List α → List α
  | [] => []
  | x :: r => x :: odds r
@[noinline] def odds {α : Type} : List α → List α
  | [] => []
  | _ :: r => evens r
end

@[noinline] def rv {α : Type} (xs : List α) : List α := xs.reverse

structure P where
  a : Nat
  b : String
deriving Repr

def main : IO Unit := do
  let ss := ["x", "y", "z", "w"]
  let ns := [1, 2, 3, 4, 5]
  let fs := [1.5, 2.5, 3.5]
  let ps := [P.mk 1 "p", P.mk 2 "q", P.mk 3 "r"]
  IO.println s!"{len ss 0} {len ns 0} {len fs 0} {len ps 0}"
  IO.println s!"{evens ss} {odds ss} {evens ns} {odds ns} {evens fs} {odds fs}"
  IO.println s!"{repr (evens ps)} {repr (odds ps)}"
  IO.println s!"{rv ss} {rv ns} {rv fs} {repr (rv ps)}"
  IO.println s!"{rv (rv ss)} {rv (rv ns)} {rv (rv fs)} {repr (rv (rv ps))}"
  -- Copies as function values.
  let lens : List (Nat → Nat) := [len ss, len ns, len fs, len ps]
  IO.println (lens.map (· 10))
  let revs : List (List String) := [ss, ["a"], []].map rv
  IO.println revs
  let revn : List (List Nat) := [ns, [7, 8]].map rv
  IO.println revn
