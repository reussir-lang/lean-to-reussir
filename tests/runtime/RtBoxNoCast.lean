/-! Runtime test: `Box` values in a program that never reads a value as
another type (no `unsafe` code of its own, no `sorry`, no axiom: plan §5.1,
`programCasts`). An unboxing function then matches only the instantiations
of its own inductive, and one whose Lean type cannot be the target's goes
through the instantiation at the shared arguments.
- `C`: values that Lean's `cse` shares between two types (`none`, `[]`,
  `some []`, `(n, [])` built at `Option Nat` and used at `Option String`),
  stored in existential packages and read by functions typed at the other
  type.
- `S`: eight structures of the same shape (`Sᵢ { a : Nat, b : String }`)
  through one polymorphically recursive function (`Prod (Array Sᵢ) Nat`,
  `Prod (Prod (Array Sᵢ) Nat) Nat`, …): each is read back at its own type,
  never at another `Sⱼ` (natively they could only meet through
  `unsafeCast`).
- `R`: the values come back from uniform code to typed code (lists of
  pairs, options of lists). -/

structure Pkg where
  α : Type
  v : α
  f : α → String

@[noinline] def run (p : Pkg) : String := p.f p.v

namespace C
def go (k : Nat) : IO Unit := do
  let p1 : Pkg := ⟨Option Nat, none, fun o => match o with | some n => s!"n{n}" | none => "nonen"⟩
  let p2 : Pkg := ⟨Option String, none, fun o => match o with | some s => s!"s{s}" | none => "nones"⟩
  let p3 : Pkg := ⟨List Nat, [], fun l => s!"{l.length}"⟩
  let p4 : Pkg := ⟨List String, [], fun l => s!"{l}"⟩
  let p5 : Pkg := ⟨Nat × List Nat, (k, []), fun l => s!"{l.1}:{l.2.length}"⟩
  let p6 : Pkg := ⟨Nat × List String, (k, []), fun l => s!"{l.1}:{l.2}"⟩
  let p7 : Pkg := ⟨Option (List Nat), some [], fun l => s!"{l.map (·.length)}"⟩
  let p8 : Pkg := ⟨Option (List String), some [], fun l => s!"{l}"⟩
  let p9 : Pkg := ⟨Option (List (Nat × String)), some [], fun l => s!"{l}"⟩
  IO.println s!"C {run p1} {run p2} {run p3} {run p4} {run p5} {run p6} {run p7} {run p8} {run p9}"
end C

namespace S
@[noinline] def grow {α : Type} (n : Nat) (x : α) (sh : α → String) : String :=
  match n with
  | 0 => sh x
  | n + 1 => grow n (x, n) (fun p => sh p.1 ++ s!"/{p.2}")

structure S0 where
  a : Nat
  b0 : String
structure S1 where
  a : Nat
  b1 : String
structure S2 where
  a : Nat
  b2 : String
structure S3 where
  a : Nat
  b3 : String
structure S4 where
  a : Nat
  b4 : String
structure S5 where
  a : Nat
  b5 : String
structure S6 where
  a : Nat
  b6 : String
structure S7 where
  a : Nat
  b7 : String

def go (k : Nat) : IO Unit := do
  IO.println (grow (k + 2) #[S0.mk k "s0"] (fun a => toString (a.map (·.b0))))
  IO.println (grow (k + 3) #[S1.mk (k + 1) "s1"] (fun a => toString (a.map (·.a))))
  IO.println (grow (k + 1) #[S2.mk k "s2", S2.mk 2 "t2"] (fun a => toString (a.map (·.b2))))
  IO.println (grow (k + 2) #[S3.mk k "s3"] (fun a => toString (a.map (·.a))))
  IO.println (grow (k + 4) #[S4.mk k "s4"] (fun a => toString (a.map (·.b4))))
  IO.println (grow (k + 2) #[S5.mk k "s5"] (fun a => toString (a.map (·.a))))
  IO.println (grow (k + 2) (S6.mk k "s6") (fun s => s.b6))
  IO.println (grow (k + 2) (some (S7.mk k "s7")) (fun s => toString (s.map (·.b7))))
end S

namespace R
@[noinline] def nest {α : Type} (n : Nat) (x : α) : List α :=
  match n with
  | 0 => [x]
  | n + 1 => (nest n (x, n)).map (·.1)

def go (k : Nat) : IO Unit := do
  let a : List (Nat × String) := nest (k + 3) (k, "x")
  let b : List (Option (List Nat)) := nest (k + 2) (some [])
  let c : List (Option (List String)) := nest (k + 2) (some [])
  let d : List (Option String) := nest (k + 1) none
  IO.println s!"R {a} {b} {c} {d}"
end R

def main (args : List String) : IO Unit := do
  let k := args.length
  C.go k
  S.go k
  R.go k
