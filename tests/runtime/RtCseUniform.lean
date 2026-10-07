/-! Runtime test: calls that Lean's mono `cse` merges across types whose
results hold function values (cross-test XT-6, review of the dependent-type
work). Natively the call runs once and its closure serves both types. An
instance at `Nat` makes a closure that reads its inputs at `Nat`, which no
conversion makes a `String → String`, so Stage 1 ran these calls apart and
their traces printed twice. Now each group of calls goes to the instance at
`lcAny` for the type arguments that differ (the uniform code, as natively),
whose closures take boxes and serve both types through wrappers; a closure
whose domain does not depend on the type argument (`Nat → Option α`) keeps
the earlier call's instance. Every trace prints once, as natively:
- `trio`: an `Option (α → α)`, at `Nat` twice and at `String`;
- `fns`: a structure with a field `run : α → α`;
- `lazy`: a thunk of a function and an array of functions;
- `pairs`: a pair of a function and a list that is empty at both types;
- `nested`: the merged partial application `tagger n` (a closure at `lcAny`)
  stored into `some` and into a list at each type;
- `dict`: a dictionary that Lean's `cse` merges across types too
  (`instInhabitedOption` at `Option Nat` and at `Option String`);
- `same`: `Option (Nat → Option α)`, the earlier call's instance;
- `cod`: `Option (Nat → α → α)`, a function whose result is a function of
  `α`: its wrappers are generated at the end of Stage 4, after the
  application function of `String → String` (`conv-liveness` gave that
  function no arm for the wrapper registered later, and rrc rejected the
  match as not exhaustive);
- `keep`: `keep n (tagger n)`, whose argument is itself a call of a group
  at `lcAny` (the partial applications `tagger n`): the uniform value serves
  at both types, so the `keep` calls merge too (they ran apart before). -/

@[noinline] def mkO {α : Type} (n : Nat) : Option (α → α) := dbgTrace s!"mkO {n}" fun _ => some id
@[noinline] def useN (o : Option (Nat → Nat)) : Nat := match o with | some f => f 5 | none => 0
@[noinline] def useS (o : Option (String → String)) : String := match o with | some f => f "s" | none => ""
def trio (n : Nat) : String := s!"{useN (mkO n) + useN (mkO n)} {useS (mkO n)}"

structure Fns (α : Type) where
  run : α → α
  name : String
@[noinline] def mkFns {α : Type} (n : Nat) : Fns α := dbgTrace s!"mkFns {n}" fun _ => ⟨id, s!"fns {n}"⟩
def fns (n : Nat) : String :=
  let a : Fns Nat := mkFns n
  let b : Fns String := mkFns n
  s!"{a.name} {a.run 5} {b.name} {b.run "s"}"

@[noinline] def mkTh {α : Type} (n : Nat) : Thunk (α → α) := dbgTrace s!"mkTh {n}" fun _ => Thunk.mk fun _ => id
@[noinline] def mkArr {α : Type} (n : Nat) : Array (α → α) := dbgTrace s!"mkArr {n}" fun _ => #[id, id]
def lazy (n : Nat) : String :=
  let t1 : Thunk (Nat → Nat) := mkTh n
  let t2 : Thunk (String → String) := mkTh n
  let a1 : Array (Nat → Nat) := mkArr n
  let a2 : Array (String → String) := mkArr n
  s!"{t1.get 7} {t2.get "t"} {a1.map (· 1)} {a2.map (· "x")}"

@[noinline] def mkP {α : Type} (n : Nat) (xs : List α) : (α → α) × List α :=
  dbgTrace s!"mkP {n}" fun _ => (id, xs)
def pairs (n : Nat) : String :=
  let p1 : (Nat → Nat) × List Nat := mkP n []
  let p2 : (String → String) × List String := mkP n []
  s!"{p1.1 3} {p1.2} {p2.1 "p"} {p2.2}"

@[noinline] def tagger {α : Type} (n : Nat) : α → α := dbgTrace s!"tagger {n}" fun _ => id
def nested (n : Nat) : String :=
  s!"{useN (some (tagger n))} {useS (some (tagger n))} {[tagger n].map (· 2)} {[tagger n].map (· "l")}"

@[noinline] def mkD {α : Type} [Inhabited α] (n : Nat) : Option (α → α) :=
  dbgTrace s!"mkD {n}" fun _ => some (fun _ => default)
@[noinline] def useDN (o : Option (Option Nat → Option Nat)) : String :=
  match o with | some f => s!"{f (some 1)}" | none => "-"
@[noinline] def useDS (o : Option (Option String → Option String)) : String :=
  match o with | some f => s!"{f (some "a")}" | none => "-"
def dict (n : Nat) : String := s!"{useDN (mkD n)} {useDS (mkD n)}"

@[noinline] def mkG {α : Type} (n : Nat) : Option (Nat → Option α) := dbgTrace s!"mkG {n}" fun _ => some fun _ => none
@[noinline] def useGN (o : Option (Nat → Option Nat)) : String := match o with | some f => s!"{f 1}" | none => "-"
@[noinline] def useGS (o : Option (Nat → Option String)) : String := match o with | some f => s!"{f 2}" | none => "-"
def same (n : Nat) : String := s!"{useGN (mkG n)} {useGS (mkG n)}"

@[noinline] def mkC {α : Type} (n : Nat) : Option (Nat → α → α) :=
  dbgTrace s!"mkC {n}" fun _ => some fun _ x => x
@[noinline] def useCN (o : Option (Nat → Nat → Nat)) : String := match o with | some f => s!"{f 1 2}" | none => "-"
@[noinline] def useCS (o : Option (Nat → String → String)) : String := match o with | some f => f 1 "c" | none => "-"
def cod (n : Nat) : String := s!"{useCN (mkC n)} {useCS (mkC n)}"

@[noinline] def tag2 {α : Type} (n : Nat) (x : α) : α := dbgTrace s!"tag {n}" fun _ => x
@[noinline] def keep {α : Type} (n : Nat) (f : α → α) : Option (α → α) := dbgTrace s!"keep {n}" fun _ => some f
def keeps (n : Nat) : String := s!"{useN (keep n (tag2 n))} {useS (keep n (tag2 n))}"

def main (args : List String) : IO Unit := do
  let n := args.length
  IO.println s!"trio {trio n}"
  IO.println s!"fns {fns n}"
  IO.println s!"lazy {lazy n}"
  IO.println s!"pairs {pairs n}"
  IO.println s!"nested {nested n}"
  IO.println s!"dict {dict n}"
  IO.println s!"same {same n}"
  IO.println s!"cod {cod n}"
  IO.println s!"keep {keeps n}"
