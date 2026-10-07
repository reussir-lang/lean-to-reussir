/-! Runtime test: one thunk crossing k times typed → uniform → typed
(blowup audit BA-19): through an existential (`Thunk (List α)`, uniform
code) and a dependent field (`Thunk (List ty.denote)`, branch `.nat`) and
back. Mode `pending`: the thunk is not forced during the loop; each crossing
makes a converting cell, and converting it back must give the original, so
no chain of cells grows (about 6 allocations per round trip through lean2rr,
3 natively). Mode `forced`: the thunk is forced before the loop; each
crossing of a forced cell converts its value, the whole list: O(n) per
round trip (8021072 allocations for 4000 round trips of a list of 1000;
natively about 3 per round trip). Either way the thunk is evaluated once
(one "eval" on stderr). The output of both modes is checked here; the
allocations of mode `pending` by tests/runtime/alloc-check.sh
(RtReprThunkChain.alloc), those of mode `forced` with RtReprThunkForced.
Arguments: MODE K N (default: both modes, 20 20). -/
inductive Ty | nat | str

@[reducible] def Ty.denote : Ty → Type
  | .nat => Nat
  | .str => String

structure PkT where
  α : Type
  t : Thunk (List α)

structure DT where
  ty : Ty
  t : Thunk (List ty.denote)

@[noinline] def viaU (p : PkT) : PkT := ⟨p.α, p.t⟩
@[noinline] def toD (_ : PkT) (t : Thunk (List Nat)) : DT := ⟨.nat, t⟩
@[noinline] def back (d : DT) (dflt : Thunk (List Nat)) : Thunk (List Nat) :=
  match d with
  | ⟨.nat, t⟩ => t
  | ⟨.str, _⟩ => dflt

@[noinline] def roundTrip (t : Thunk (List Nat)) : Thunk (List Nat) :=
  -- typed → uniform (existential) → dependent → typed
  match viaU ⟨Nat, t⟩ with
  | ⟨_, _⟩ => back (toD ⟨Nat, t⟩ t) t

def run (mode : String) (k n : Nat) : IO Unit := do
  let t0 : Thunk (List Nat) := Thunk.mk fun _ => dbgTrace s!"eval {mode}" fun _ => List.range n
  if mode == "forced" then IO.println s!"before {t0.get.length}"
  let mut t := t0
  for _ in [0:k] do
    t := roundTrip t
  IO.println s!"{mode} after {t.get.length} {t0.get.length}"

def main (args : List String) : IO Unit := do
  let k := (args.getD 1 "20").toNat!
  let n := (args.getD 2 "20").toNat!
  match args.head? with
  | some m => run m k n
  | none => do run "pending" k n; run "forced" k n
