/-! Runtime test: closed calls (closed terms, which Lean's closed-term
extraction shares between functions when value and type agree) of
functions whose calls Lean's mono `cse` merges across types. Every trace
prints as natively.
- `shared`: `mkO 3 : Option (α → α)` in `one` at `Nat`, in `two` at
  `String`, and in `both` at `Nat` and then `String`. A closure at
  `Nat → Nat` does not serve as `String → String`; the instance at `lcAny`
  would be a closed term of its own (three traces: review of the
  dependent-type work), so `both`'s calls run apart, each sharing the
  closed term of `one` or `two`: two traces, as natively. `mkO 4` in
  `bothRev` at `String` and then `Nat`, and in `oneB` at `Nat`: two traces.
- `hidden`: `mkLen 3`, whose result type does not show `α`
  (`Option ((b : Bool) → (if b then List α else Unit) → Nat)` is
  `Option (Bool → lcAny → Nat)` at every `α`): natively one closed term
  for every call at every `α`, so one trace. A type parameter that shows
  nowhere in the declaration's type gets the instance at `lcAny` at every
  call (`Mono.typeParamHidden`), so the calls in `hOne`, `hTwo` and `hBoth`
  are one closed term (they printed three traces before).
- `phantom`: `ph (α := Nat) 5` in `p1` and `ph (α := String) 5` in `p2`:
  one instance, one closed term, one trace (two before). -/

namespace Shared
@[noinline] def mkO {α : Type} (n : Nat) : Option (α → α) := dbgTrace s!"mkO {n}" fun _ => some id
@[noinline] def useN (o : Option (Nat → Nat)) : Nat := match o with | some f => f 5 | none => 0
@[noinline] def useS (o : Option (String → String)) : String := match o with | some f => f "s" | none => ""
@[noinline] def one (k : Nat) : Nat := useN (mkO 3) + k
@[noinline] def two (k : Nat) : String := useS (mkO 3) ++ toString k
@[noinline] def both (k : Nat) : String := s!"{useN (mkO 3)} {useS (mkO 3)} {k}"
@[noinline] def bothRev (k : Nat) : String := s!"{useS (mkO 4)} {useN (mkO 4)} {k}"
@[noinline] def oneB (k : Nat) : Nat := useN (mkO 4) + k
end Shared

namespace Hidden
@[noinline] def mkLen {α : Type} (n : Nat) : Option ((b : Bool) → (if b then List α else Unit) → Nat) :=
  dbgTrace s!"mkLen {n}" fun _ => some fun b v => match b, v with | true, xs => xs.length | false, _ => 0
@[noinline] def lN (o : Option ((b : Bool) → (if b then List Nat else Unit) → Nat)) : Nat :=
  match o with | some f => f true [1, 2] | none => 0
@[noinline] def lS (o : Option ((b : Bool) → (if b then List String else Unit) → Nat)) : Nat :=
  match o with | some f => f true ["a"] | none => 0
@[noinline] def hOne (k : Nat) : Nat := lN (mkLen 3) + k
@[noinline] def hTwo (k : Nat) : Nat := lS (mkLen 3) + k
@[noinline] def hBoth (k : Nat) : String := s!"{lN (mkLen 3)} {lS (mkLen 3)} {k}"
end Hidden

namespace Phantom
@[noinline] def ph {α : Type} (n : Nat) : Nat := dbgTrace s!"ph {n}" fun _ => n + 1
@[noinline] def p1 (k : Nat) : Nat := ph (α := Nat) 5 + k
@[noinline] def p2 (k : Nat) : Nat := ph (α := String) 5 + k
end Phantom

def main (args : List String) : IO Unit := do
  let k := args.length
  IO.println s!"shared {Shared.one k} {Shared.two k} {Shared.both k}"
  IO.println s!"shared {Shared.bothRev k} {Shared.oneB k}"
  IO.println s!"hidden {Hidden.hOne k} {Hidden.hTwo k} {Hidden.hBoth k}"
  IO.println s!"phantom {Phantom.p1 k} {Phantom.p2 k}"
