/-! Runtime test: a `[value]` struct whose one field is a function value,
put into boxes and taken out. A recursive structure with one field (Lean
keeps it, `hasTrivialStructure?` excludes recursive types) is lean2rr's
`struct [value] T_Gen(L2RFn_…)`; one field over another such struct (a
mutual pair) nests two of them. Unboxing such a struct unboxed its field
at the function type with the in-line unboxing, which has no case for a
function value: lean2rr stopped with "boxUnbox at function type (internal
error)". The field is now read by the generated unboxing of its function
type. Values: generators in a list, an array, an `Option`, a pair, a
thunk, a generic function's result. -/
inductive Gen where
  | mk : (Nat → Option (Nat × Gen)) → Gen

instance : Inhabited Gen := ⟨.mk fun _ => none⟩

mutual
inductive C where
  | mk : D → C
inductive D where
  | mk : (Nat → Option (Nat × C)) → D
end

instance : Inhabited C := ⟨.mk (.mk fun _ => none)⟩

partial def counter (k : Nat) : Gen :=
  .mk fun x => if x > 100 then none else some (x + k, counter (k + 1))

partial def cnt (k : Nat) : C :=
  .mk (.mk fun x => if x > 100 then none else some (x * k, cnt (k + 2)))

@[noinline] def step : Gen → Nat → Option (Nat × Gen)
  | .mk f, x => f x

@[noinline] def stepC : C → Nat → Option (Nat × C)
  | .mk (.mk f), x => f x

/-- The first `n` values of `g` from `x`. -/
def run : Nat → Gen → Nat → List Nat
  | 0, _, _ => []
  | n + 1, g, x => match step g x with
    | some (a, g') => a :: run n g' x
    | none => []

def runC : Nat → C → Nat → List Nat
  | 0, _, _ => []
  | n + 1, g, x => match stepC g x with
    | some (a, g') => a :: runC n g' x
    | none => []

@[noinline] def rev {α : Type} (xs : List α) : List α := xs.reverse
@[noinline] def pick {α : Type} (b : Bool) (x y : α) : α := if b then x else y

def main : IO Unit := do
  let gs : List Gen := [counter 1, counter 10, default]
  IO.println ((rev gs).map (run 3 · 5))
  let arr : Array Gen := #[counter 2, counter 20]
  IO.println (run 2 arr[1]! 1, run 2 arr[7]! 1)
  let o : Option Gen := some (counter 7)
  IO.println (o.map (run 2 · 0))
  let p : Gen × Nat := (counter 3, 4)
  IO.println (run 3 p.1 p.2)
  let t : Thunk Gen := Thunk.mk fun _ => counter 5
  IO.println (run 2 t.get 1)
  IO.println (run 3 (pick false (counter 0) (counter 100)) 1)
  let cs : List C := [cnt 1, cnt 3]
  IO.println ((rev cs).map (runC 3 · 2))
