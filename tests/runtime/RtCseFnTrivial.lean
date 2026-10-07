/-! Runtime test: a call that Lean's mono `cse` merges across types whose
result is a one-field structure around a function at one instantiation and
a function type at the other (review of XT-6 round 3,
rv7/frontend/xt6/round3 XT6-04). `Fn` is a trivial structure: natively, and
in mono, an `Fn` is its field, a closure. So `choose [] ⟨tagger n⟩` (at `Fn`)
and `choose [] (tagger n)` (at `String → String`) are one call: `Fn.mk t` is
`t`, and the two partial applications `tagger n` merge. Stage 1 took
`Fn` and `String → String` for types with no common value and aligned the
second call to `Fn`. Its value, a `Nat → Nat` closure, used at
`String → String`, needed a conversion that does not exist ("no
representation conversion from L2RFn_F3nNat3nNat to L2RFn_F4nLStr4nLStr"):
"INTERNAL PANIC: unreachable code has been reached". `Mono.serves` compares
the types as `toMono` sees them (`monoHead`: `Fn` is `Nat → Nat`), so the
call is not aligned to the earlier call's instance. The partial
applications `tagger n` go to the instance at `lcAny`; the `choose` calls
cannot, since the earlier call's argument `⟨tagger n⟩` is an `Fn` (a
`Nat → Nat`), which does not serve as the later call's `String → String`:
they run twice, as plan §10 "Merging after erasure" says (the trace is in
the closure, run per application). -/

@[noinline] def tagger {α : Type} (n : Nat) (x : α) : α := dbgTrace s!"tag {n}" fun _ => x

structure Fn where
  f : Nat → Nat

@[noinline] def choose {α : Type} (xs : List α) (d : α) : α := xs.headD d

@[noinline] def applyTo {α : Type} (f : α → α) (x : α) : α := f x

def main (args : List String) : IO Unit := do
  let n := args.length
  let a : Fn := choose [] ⟨tagger n⟩
  let b : String → String := choose [] (tagger n)
  IO.println s!"{applyTo a.f 5} {applyTo b "s"}"
