/-! Runtime test: calls that Lean's mono `cse` merges across types in shapes
the first XT-6 alignment missed (review rv7/frontend/xt6 XT6-02), where a
trace or panic inside printed twice instead of once.
- `dict`: the dictionaries agree after erasure (`instInhabitedOption` at two
  types, no value arguments; `Inhabited` is weak_specialize, so natively no
  specialization). Only the type arguments were aligned, and the second call
  kept its own dictionary, a mixed instance: the later call now takes the
  earlier call's arguments entirely.
- `subtype`: `some ⟨5, h⟩ : Option {n // n > 0}` and `some 5 : Option Nat`
  are one value in mono (a `Subtype` is its value), so Lean merges the two
  calls of `gp`; Stage 1 compared base values, where they differ. It now
  takes a trivial structure for its field (and `Decidable` for `Bool`), as
  `toMono` does. -/

@[noinline] def dflt {α : Type} [Inhabited α] (n : Nat) : List α :=
  dbgTrace s!"dflt {n}" fun _ => List.replicate n default

@[noinline] def useA (xs : List (Option Nat)) : Nat := xs.length
@[noinline] def useB (xs : List (Option String)) : Nat := xs.length + 100

def dict (n : Nat) : Nat :=
  let a : List (Option Nat) := dflt n
  let b : List (Option String) := dflt n
  useA a + useB b

@[noinline] def gp {α : Type} (xs : Array Nat) (x : Option α) : Option α :=
  if xs[5]! > 3 then x else none

@[noinline] def useP (o : Option {n : Nat // n > 0}) : Nat := match o with | some p => p.val | none => 1
@[noinline] def useN (o : Option Nat) : Nat := match o with | some n => n | none => 2

def subtype (xs : Array Nat) : Nat :=
  let p : {n : Nat // n > 0} := ⟨5, by decide⟩
  useP (gp xs (some p)) + useN (gp xs (some 5))

def main (args : List String) : IO Unit := do
  IO.println s!"dict {dict (args.length + 2)}"
  IO.println s!"subtype {subtype (Array.range args.length)}"
