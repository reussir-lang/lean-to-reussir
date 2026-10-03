/-! Runtime test: a call that Lean's CSE merges across types (XT-6, leanrs
A482). Lean's mono-phase `cse` compares values with type arguments erased,
so `gp xs none` used as an `Option String` and later as an
`Option (Nat → Nat)` is one call: its panic prints once. Stage 1 made an
instance per type, so the call ran twice and the panic printed twice. The
later call is now made at the first call's type arguments, so Stage 2's
`cse` merges the two as natively, and the value is converted where it is
used at the other type. Lean's closed-term cache compares types, so a closed
call at two types in two functions runs twice, natively too; in one function
the merged call reads the first function's closed term. -/

@[noinline] def gp {α} (xs : Array Nat) (k : Nat) (x : Option α) : Option α :=
  if xs[k]! > 3 then x else none
@[noinline] def useS (o : Option String) : Nat := match o with | some s => s.length | none => 1
@[noinline] def useF (o : Option (Nat → Nat)) : Nat := match o with | some f => f 3 | none => 2

-- The repro: the panic prints once.
def direct (xs : Array Nat) : Nat := useS (gp xs 5 none) + useF (gp xs 5 none)

-- A482's shape: a literal index, the size added.
def kernel (xs : Array Nat) : Nat := useS (gp xs 2 none) + useF (gp xs 2 none) + xs.size

-- A trace in the callee, and a list of values that agree after erasure,
-- matched at both types.
@[noinline] def tr {α} (n : Nat) (x : Option α) : List (Option α) :=
  dbgTrace s!"tr {n}" fun _ => List.replicate n x

def lists (n : Nat) : Nat :=
  let a : List (Option String) := tr n none
  let b : List (Option (Nat → Nat)) := tr n none
  a.foldl (fun acc o => acc + useS o) 0 + b.foldl (fun acc o => acc + useF o) 0

-- Closed calls at two types, in one function and in two.
@[noinline] def gq {α} (xs : Array Nat) (x : Option α) : Option α :=
  dbgTrace "gq" fun _ => if xs[1]! > 3 then x else none
@[noinline] def one (k : Nat) : Nat := useS (gq #[1, 2, 3] none) + k
@[noinline] def two (k : Nat) : Nat := useF (gq #[1, 2, 3] none) + k
@[noinline] def both (k : Nat) : Nat := useS (gq #[1, 2, 3] none) + useF (gq #[1, 2, 3] none) + k

-- A polymorphic constant (only a type parameter) at two types: one closed
-- term after the merge.
@[noinline] def el {α : Type} : List α := dbgTrace "el" fun _ => []
@[noinline] def lens (k : Nat) : Nat := (el : List Nat).length + (el : List String).length + k

def main (args : List String) : IO Unit := do
  let xs := Array.range args.length
  IO.println s!"direct {direct xs}"
  IO.println s!"kernel {kernel xs} {kernel (Array.range 6)}"
  IO.println s!"lists {lists (args.length + 3)}"
  IO.println s!"closed {one args.length} {two args.length} {both args.length}"
  IO.println s!"lens {lens args.length} {lens (args.length + 1)}"
