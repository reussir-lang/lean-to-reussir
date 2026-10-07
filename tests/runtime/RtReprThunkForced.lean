/-! Runtime test: one forced thunk crossing k times typed → uniform → typed
(blowup audit BA-19, mode `forced`; RtReprThunkChain runs both modes and
checks the pending one's allocations): through an existential
(`Thunk (List α)`, uniform code) and a dependent field
(`Thunk (List ty.denote)`, branch `.nat`) and back. The thunk is forced
before the loop, and each crossing of a forced cell converts its value,
the whole list: O(n) per round trip (8021072 allocations for 4000 round
trips of a list of 1000; natively about 3 per round trip). It is evaluated
once (one "eval" on stderr). The output is checked here; the allocations
by tests/runtime/alloc-check.sh (RtReprThunkForced.alloc). Arguments: K N
(default 20 20). -/
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

def main (args : List String) : IO Unit := do
  let k := (args.getD 0 "20").toNat!
  let n := (args.getD 1 "20").toNat!
  let t0 : Thunk (List Nat) := Thunk.mk fun _ => dbgTrace "eval" fun _ => List.range n
  IO.println s!"before {t0.get.length}"
  let mut t := t0
  for _ in [0:k] do
    t := roundTrip t
  IO.println s!"after {t.get.length} {t0.get.length}"
