/-! Runtime test: a function value that goes through uniform code and back
at every step (blowup audit, repeated crossings, probe FnRoundTrip), at
three representations (`Nat → Nat` typed, `Nat → Box` and `Box → Box` in
the two packages), and is called at each step. Converting a function value
wraps it; converting a wrapper back must give the function, not a wrapper
of a wrapper: if wrappers stacked, each call would cost O(step) and the
chain would grow (quadratic time, linear memory). Through lean2rr each
round trip makes a constant number of allocations (3; natively 1). The
output is checked here; the allocations by tests/runtime/alloc-check.sh
(RtReprFnRoundTrip.alloc). -/
inductive Ty | nat | str

@[reducible] def Ty.denote : Ty → Type
  | .nat => Nat
  | .str => String

structure Fn1 where
  t : Ty
  f : t.denote → t.denote

structure Fn2 where
  t : Ty
  f : Nat → t.denote

@[noinline] def via1 (p : Fn1) : Fn1 := ⟨p.t, p.f⟩
@[noinline] def via2 (p : Fn2) : Fn2 := ⟨p.t, p.f⟩

def main (args : List String) : IO Unit := do
  let n := (args.headD "1000").toNat!
  let mut g : Nat → Nat := (· + 1)
  let mut acc := 0
  for i in [0:n] do
    match via1 ⟨.nat, g⟩ with
    | ⟨.nat, f⟩ =>
      match via2 ⟨.nat, f⟩ with
      | ⟨.nat, h⟩ => g := h; acc := acc + h i
      | _ => pure ()
    | _ => pure ()
  IO.println (acc + g 0)
