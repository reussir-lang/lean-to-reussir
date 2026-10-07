/-! Runtime test: a function polymorphic in `α : Type u` instantiated at a
type whose values are types (`Type`, `Type → Type`; adversarial review of
the dependent-type work, K3, also K2 and TypesAsData). Natively `apTwice` is
one function with `x y : lcAny` (given `box(0)`), so `f x + f y` applies `f`
twice and `k2`'s trace or `kpan`'s panic comes out twice. Stage 1's instance
at `α := Type` typed `x` and `y` as `Type`, which Lean's passes take for
type parameters: erased, removed by `reduceArity`, every use the literal
`◾`, and Lean's `cse` merged `f ◾` and `f ◾`, so the trace and the panic
came out once (cases A, E, J, K). A type argument whose values are types now
gives the uniform instance (`Mono.renameApp`), whose `x y : lcAny` stay data,
as natively. The other cases already agreed and must stay so: a proposition
(`apTwiceP`: proofs are erased natively too, one trace), `Unit` values, a
proposition as the type (`apTwiceS kpf`), lists and arrays of types, and
`twoCalls f x = f x + f x` (merged natively too). -/
set_option linter.unusedVariables false
def k2 (α : Type) : Nat := dbgTrace "k2" fun _ => 2
def ku (u : Unit) : Nat := dbgTrace "ku" fun _ => 3
def kpf (h : 1 = 1) : Nat := dbgTrace "kpf" fun _ => 4
def kpan (α : Type) : Nat := panic! "kpan"
def kt (F : Type → Type) : Nat := dbgTrace "kt" fun _ => 5

@[noinline] def apTwice {α : Type u} (f : α → Nat) (x y : α) : Nat := f x + f y
@[noinline] def apTwiceP {p : Prop} (f : p → Nat) (x y : p) : Nat := f x + f y
@[noinline] def apTwiceS {α : Sort u} (f : α → Nat) (x y : α) : Nat := f x + f y
@[noinline] def apList {α : Type u} (f : α → Nat) (xs : List α) : Nat := xs.foldl (fun acc x => acc + f x) 0
@[noinline] def apArr {α : Type u} (f : α → Nat) (xs : Array α) : Nat := xs.foldl (fun acc x => acc + f x) 0
@[noinline] def twoCalls {α : Type u} (f : α → Nat) (x : α) : Nat := f x + f x

def main : IO Unit := do
  IO.eprintln "A: apTwice k2 Nat Nat (native: 2)"
  IO.println s!"{apTwice k2 Nat Nat}"
  IO.eprintln "B: apTwice k2 Nat String"
  IO.println s!"{apTwice k2 Nat String}"
  IO.eprintln "C: apTwice ku () ()"
  IO.println s!"{apTwice ku () ()}"
  IO.eprintln "D: apTwiceP kpf rfl rfl"
  IO.println s!"{apTwiceP kpf rfl rfl}"
  IO.eprintln "E: apTwiceS k2 Nat Nat"
  IO.println s!"{apTwiceS k2 Nat Nat}"
  IO.eprintln "F: apTwiceS kpf rfl rfl"
  IO.println s!"{apTwiceS kpf rfl rfl}"
  IO.eprintln "G: apList k2 [Nat, String, Float]"
  IO.println s!"{apList k2 [Nat, String, Float]}"
  IO.eprintln "H: apArr k2 #[Nat, Bool]"
  IO.println s!"{apArr k2 #[Nat, Bool]}"
  IO.eprintln "I: twoCalls k2 Nat (native: 2)"
  IO.println s!"{twoCalls k2 Nat}"
  IO.eprintln "J: apTwice kt List Option"
  IO.println s!"{apTwice kt List Option}"
  IO.eprintln "K: apTwice kpan Nat Nat (panic twice natively)"
  IO.println s!"{apTwice kpan Nat Nat}"
  IO.eprintln "end"
