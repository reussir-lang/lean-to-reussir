/-! Runtime test: the calls that Lean's mono `cse` merges across types and
lean2rr still runs apart or more often (plan §10, "Merging after erasure").
Lean does not fix how often a trace in pure code prints, so the test records
both runs' stderr (`RtCseApart.native.err`, `RtCseApart.l2r.err`) and fails
if either changes.
- `closed`: `mkO 3`, a closed call, in `one` at `Option (Nat → Nat)` and in
  `both` at `Option (Nat → Nat)` and then `Option (String → String)`.
  Natively `both`'s merged call keeps the earlier type and is the closed
  term of `one` (Lean's closed-term cache compares values and types): one
  trace for `mkO 3`. A closure at `Nat → Nat` does not serve as
  `String → String`, and the instance at `lcAny` would be a closed term of
  its own, so `both`'s calls run apart, as before the review of the
  dependent-type work: two traces (the Nat call shares `one`'s term).
- `field`: `mkFoo 3`, a closed call, in `fOne` at `Foo Nat` and in `fBoth`
  at `Foo Nat` and then `Foo String`, where `Foo`'s field `val` is
  `lcAny` (`(b : Bool) → if b then List α else Unit`), which can hide the
  type argument. The calls go to the instance at `lcAny`, as the base (which
  aligned them to the earlier call's instance) merged them too, but its
  closed term is not `fOne`'s: `mkFoo 3` prints twice, natively and on the
  base once; `mkFoo 4`, in `gBoth` alone, once, as natively.
- `jp`: `mkL n` at `List Nat` before an `if` and at `List String` in the
  join point after it. Stage 1 sees the first call moved into the branch
  that uses it, out of the join point's scope; natively Lean's later passes
  inline the join point into that branch, and `cse` merges the calls there:
  `mkL 0` prints once per run of `jp` natively, and twice through lean2rr
  when `c` is true. -/

namespace Closed
@[noinline] def mkO {α : Type} (n : Nat) : Option (α → α) := dbgTrace s!"mkO {n}" fun _ => some id
@[noinline] def useN (o : Option (Nat → Nat)) : Nat := match o with | some f => f 5 | none => 0
@[noinline] def useS (o : Option (String → String)) : String := match o with | some f => f "s" | none => ""
@[noinline] def one (k : Nat) : Nat := useN (mkO 3) + k
@[noinline] def both (k : Nat) : String := s!"{useN (mkO 3)} {useS (mkO 3)} {k}"
end Closed

namespace Field
structure Foo (α : Type) where
  x : Option α
  val : (b : Bool) → if b then List α else Unit
@[noinline] def mkFoo {α : Type} (n : Nat) : Foo α :=
  dbgTrace s!"mkFoo {n}" fun _ => ⟨none, fun b => match b with | true => [] | false => ()⟩
@[noinline] def useFN (f : Foo Nat) : Nat := f.x.getD 0
@[noinline] def useFS (f : Foo String) : String := f.x.getD "-"
@[noinline] def fOne (k : Nat) : Nat := useFN (mkFoo 3) + k
@[noinline] def fBoth (k : Nat) : String := s!"{useFN (mkFoo 3)} {useFS (mkFoo 3)} {k}"
@[noinline] def gBoth (k : Nat) : String := s!"{useFN (mkFoo 4)} {useFS (mkFoo 4)} {k}"
end Field

namespace Jp
@[noinline] def mkL {α : Type} (n : Nat) : List α := dbgTrace s!"mkL {n}" fun _ => []
@[noinline] def jp (n : Nat) (c : Bool) : String :=
  let a : List Nat := mkL n
  let r := if c then a else [1]
  let b : List String := mkL n
  let s := match r with | x :: _ => toString x | [] => "-"
  s ++ " " ++ toString b
end Jp

def main (args : List String) : IO Unit := do
  IO.println s!"closed {Closed.one args.length} {Closed.both args.length}"
  IO.println s!"field {Field.fOne args.length} {Field.fBoth args.length} {Field.gBoth args.length}"
  IO.println s!"jp {Jp.jp args.length true} {Jp.jp args.length false}"
